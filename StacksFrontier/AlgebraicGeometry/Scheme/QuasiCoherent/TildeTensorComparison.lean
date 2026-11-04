module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The comparison morphism `(M ⊗_R N)~ ⟶ M̃ ⊗ Ñ` and its germs

For modules `M` and `N` over a commutative ring `R`, Stacks 01I8 asserts among other things that
the associated-sheaf construction on `Spec R` is compatible with tensor products:
`M̃ ⊗_{𝒪_{Spec R}} Ñ ≅ (M ⊗_R N)~`.  This file constructs the canonical morphism underlying that
assertion, computes it on sections and on stalks, and proves that it is an isomorphism.

The morphism is built as the adjoint transpose, under `AlgebraicGeometry.tilde.adjunction`, of a
map of `R`-modules `M ⊗_R N ⟶ Γ(Spec R, M̃ ⊗ Ñ)`, which is in turn assembled from the canonical
sections `AlgebraicGeometry.tilde.toOpen` of `M̃` and `Ñ` and the section map
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` of the sheafified tensor
  product.  Transposing in this
direction is what makes the germ computation available: the two Mathlib characterisations
`AlgebraicGeometry.tilde.toOpen_map_app` and
`AlgebraicGeometry.Scheme.Modules.toOpen_fromTildeΓ_app` compute the transpose on the image of
`toOpen`, and `AlgebraicGeometry.tilde.toStalk` is by definition the germ at `⊤` of `toOpen`, so
the stalk map is determined on the image of `toStalk` — which is exactly the generating set an
`IsLocalizedModule` argument needs.

## Main definitions

* `topTensorMap`: the canonical map of `R`-modules `M ⊗_R N ⟶ Γ(Spec R, M̃ ⊗ Ñ)`, sending a pure
  tensor `m ⊗ n` to the image under
    `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` of the tensor of the two
  canonical global sections.
* `tildeTensorComparison`: the comparison morphism `(M ⊗_R N)~ ⟶ M̃ ⊗ Ñ`, the adjoint transpose
  of `topTensorMap`.
* `toStalkL`: `AlgebraicGeometry.tilde.toStalk`, retyped at the Tag 01CB spelling of the stalk, so
  that the Tag 01CB stalk machinery and Mathlib's `IsLocalizedModule` instance apply to the same
  term.

## Main results

* `tildeTensorComparison_app_top`: on global sections the comparison morphism is `topTensorMap`.
* `tildeTensorComparison_stalkMapL_toStalk`: the stalk map of the comparison morphism carries the
  image under `toStalk` of `z : M ⊗_R N` to the germ of `topTensorMap z`.
* `tensorStalkIso_stalkMapL_toStalkL`: composed with the Tag 01CB identification
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` of the stalk of a tensor product,
    the stalk map of the comparison
  carries `toStalk (m ⊗ n)` to `toStalk m ⊗ toStalk n`.  This is the germ characterisation of the
  comparison morphism.
* `isIso_tildeTensorComparison` and `tildeTensorIso`: **the tensor half of Stacks 01I8** --- the
  comparison morphism is an isomorphism, so `(M ⊗_R N)~ ≅ M̃ ⊗ Ñ`.
* `stalkModule_eq_presheafModule`: the Tag 01CB module structure on the stalk of a presheaf of
  modules over the structure sheaf of a scheme agrees with the `PresheafOfModules` one.
* `towerStalk`: consequently the `R`-action on the stalk of `Ã` is the restriction of the
  `𝒪_{Spec R, x}`-action along `R ⟶ 𝒪_{Spec R, x}`.  This is what lets the Tag 01CB tensor
  product over the stalk ring be compared with Mathlib's localization statements over `R`.

## Implementation notes

Four `rfl`-equal spellings of the structure sheaf of `Spec R` occur, and neither instance search
nor `rw` crosses between them, although terms do.  In this file:

* `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` — the `𝒪_{X,x}`-module structure on a
  stalk that
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is stated over — is found only when
    the *point* is written at the
  spelling `((Spec R).toRingedSpace.carrier : Type u)`, while Mathlib's `tilde` instances
  (`StructureSheaf.stalkAlgebra`, `IsLocalization.to_stalk`, the `IsLocalizedModule` instance on
  `tilde.toStalk` and the `Module R` structure on a stalk) are found only with the point written
  as `PrimeSpectrum.Top R`.  The two types are `rfl`-equal, so `pt` retypes the point and the
  Mathlib-side structures are seated by `inferInstanceAs` against it; this is why `moduleRStalk`
  and `isLocalizedModule_toStalkL` exist rather than being found.
* `rw` is unusable on goals mentioning both spellings — it reports the target not type-correct
  under implicit transparency — so the proofs below are term mode, and the elementwise form of a
  categorical identity is taken with `DFunLike.congr_fun (congrArg ModuleCat.Hom.hom _)` rather
  than with `simpa`, which normalises into the other spelling and then fails to close the goal.
* `tildeSheaf` and `tildeTensor` do the crossing once each, on bare variables.

### The argument for invertibility

Invertibility is checked on stalks.  `tensorStalkIso_stalkMapL_toStalkL` identifies the stalk map
of the comparison on the image of `toStalk`, and that image is exactly a generating set for an
`IsLocalizedModule` argument: `AlgebraicGeometry.tilde.toStalk` exhibits the stalk of `(M ⊗_R N)~`
as a localization of `M ⊗_R N` at the prime, and `TensorProduct.map` of the two localization maps
exhibits `M_x ⊗_R N_x` as another, by Mathlib's `IsLocalization` instance.  A map between two
localizations of one module which commutes with the localization maps is invertible, which is
`ModuleCat.isIso_of_isLocalizedModule_comp`.

Two conversions are needed to line those up, and they are the only real work beyond the germ
formula.  The tensor product in the Tag 01CB identification is over `𝒪_{X,x}` while Mathlib's
instance is over `R`; `IsLocalization.moduleTensorEquiv` converts between them, using that the
structure-sheaf stalk is a localization of `R`.  It needs the scalar tower `towerStalk`, which in
turn needs `stalkModule_eq_presheafModule`.

`stalkModule_eq_presheafModule` is `rfl`: the Tag 01CB name for the stalk module structure is
Mathlib's instance by definition.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.TildeTensor

/-! ### Two transport utilities -/

/-- Transport an `IsScalarTower` along an equality of the middle module structure. -/
lemma tower_transport {Rr S Mm : Type u} [CommRing Rr] [CommRing S] [Algebra Rr S]
    [AddCommGroup Mm] [Module Rr Mm] {i j : Module S Mm} (hij : i = j)
    (h : letI := j; IsScalarTower Rr S Mm) : letI := i; IsScalarTower Rr S Mm := by
  cases hij; exact h

/-- **The two names for the module structure on the stalk of a presheaf of modules over the
structure sheaf of a scheme agree**: the Tag 01CB name
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` is the `PresheafOfModules` instance,
by definition. -/
lemma stalkModule_eq_presheafModule {X : Scheme.{u}}
    (F : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toSheafedSpace F x =
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F x :=
  rfl

variable {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)

/-! ### Crossing between the two spellings of the category of modules on `Spec R` -/

/-- `M̃`, retyped over `structureSheafRing`, which is
  the spelling
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` is indexed by.  A reducible retyping
  across a `rfl`-equality of the
two spellings of the structure sheaf; it is done here, once, on a bare variable. -/
abbrev tildeSheaf (A : ModuleCat.{u} R) :
    SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace) := tilde A

/-- The tensor product `M̃ ⊗ Ñ`, retyped as an object of `(Spec R).Modules`, which is the spelling
Mathlib's `tilde` machinery is indexed by. -/
abbrev tildeTensor : (Spec R).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N)))

/-! ### The canonical global sections and the map on global sections -/

/-- The scalar in `𝒪_{Spec R}(⊤)` through which `r : R` acts on global sections.  This is the
scalar named by `AlgebraicGeometry.Scheme.Modules.smul_Spec_def`. -/
def cTop (r : R) : (Spec R).presheaf.obj (op ⊤) :=
  ((Spec R).presheaf.map (Opens.leTop ⊤).op).hom (((Scheme.ΓSpecIso R).inv).hom r)

/-- The canonical global section of `Ã` attached to `a : A`, at the Tag 01CB spelling. -/
def topSec (A : ModuleCat.{u} R) (a : A) : (tildeSheaf A).val.obj (op ⊤) :=
  (tilde.toOpen A ⊤).hom a

/-- `topSec` is semilinear over `r ↦ cTop r`: the `R`-action on global sections is the
`𝒪_{Spec R}(⊤)`-action through `cTop`. -/
lemma topSec_smul (A : ModuleCat.{u} R) (r : R) (a : A) :
    topSec A (r • a) = cTop r • topSec A a :=
  (map_smul (tilde.toOpen A ⊤).hom r a).trans
    (Scheme.Modules.smul_Spec_def (M := tilde A) r ((tilde.toOpen A ⊤).hom a))

/-- `topSec` is additive. -/
lemma topSec_add (A : ModuleCat.{u} R) (a a' : A) :
    topSec A (a + a') = topSec A a + topSec A a' :=
  map_add (tilde.toOpen A ⊤).hom a a'

/-- The global section of `M̃ ⊗ Ñ` attached to a pair `(m, n)`: the image under
`Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` of the tensor of the two
  canonical sections. -/
def topTmul (m : M) (n : N) : Γ(tildeTensor M N, ⊤) :=
  toTensorSheafSection (Spec R).toRingedSpace (tildeSheaf M) (tildeSheaf N) (op ⊤)
    (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n)

/-- `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` is `𝒪_{Spec R}(⊤)`-linear
  in its scalar. -/
lemma toTS_smul (c : (Spec R).presheaf.obj (op ⊤))
    (t : TensorProduct ((Spec R).presheaf.obj (op ⊤))
      ((tildeSheaf M).val.obj (op ⊤)) ((tildeSheaf N).val.obj (op ⊤))) :
    toTensorSheafSection (Spec R).toRingedSpace (tildeSheaf M) (tildeSheaf N) (op ⊤) (c • t)
      = @HSMul.hSMul _ Γ(tildeTensor M N, ⊤) _ _ c
          (toTensorSheafSection (Spec R).toRingedSpace (tildeSheaf M) (tildeSheaf N) (op ⊤) t) :=
  map_smul ((sheafifyUnit (Spec R).toRingedSpace
    ((PresheafOfModules.tensorObj (O := ((Spec R).toRingedSpace).presheaf) ((tildeSheaf M).val) ((tildeSheaf N).val)))).app (op ⊤)).hom
    c t

/-- `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` is additive. -/
lemma toTS_add (t t' : TensorProduct ((Spec R).presheaf.obj (op ⊤))
      ((tildeSheaf M).val.obj (op ⊤)) ((tildeSheaf N).val.obj (op ⊤))) :
    toTensorSheafSection (Spec R).toRingedSpace (tildeSheaf M) (tildeSheaf N) (op ⊤) (t + t')
      = toTensorSheafSection (Spec R).toRingedSpace (tildeSheaf M) (tildeSheaf N) (op ⊤) t
        + toTensorSheafSection (Spec R).toRingedSpace (tildeSheaf M) (tildeSheaf N) (op ⊤) t' :=
  map_add ((sheafifyUnit (Spec R).toRingedSpace
    ((PresheafOfModules.tensorObj (O := ((Spec R).toRingedSpace).presheaf) ((tildeSheaf M).val) ((tildeSheaf N).val)))).app (op ⊤)).hom
    t t'

/-- `topTmul` is semilinear over `cTop` in its left argument. -/
lemma topTmul_smul_left (r : R) (m : M) (n : N) :
    topTmul M N (r • m) n = cTop r • topTmul M N m n := by
  have h1 : topSec M (r • m) ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n
      = (cTop r • topSec M m) ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n :=
    congrArg (· ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n) (topSec_smul M r m)
  have h2 : (cTop r • topSec M m) ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n
      = cTop r • (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n) :=
    TensorProduct.smul_tmul' _ _ _
  exact (congrArg _ (h1.trans h2)).trans (toTS_smul M N (cTop r) _)

/-- `topTmul` is semilinear over `cTop` in its right argument. -/
lemma topTmul_smul_right (r : R) (m : M) (n : N) :
    topTmul M N m (r • n) = cTop r • topTmul M N m n := by
  have h1 : topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N (r • n)
      = topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] (cTop r • topSec N n) :=
    congrArg (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] ·) (topSec_smul N r n)
  have h2 : topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] (cTop r • topSec N n)
      = cTop r • (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n) :=
    TensorProduct.tmul_smul _ _ _
  exact (congrArg _ (h1.trans h2)).trans (toTS_smul M N (cTop r) _)

/-- `topTmul` is additive in its left argument. -/
lemma topTmul_add_left (m m' : M) (n : N) :
    topTmul M N (m + m') n = topTmul M N m n + topTmul M N m' n := by
  have h1 : topSec M (m + m') ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n
      = (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n)
        + (topSec M m' ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n) :=
    (congrArg (· ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n) (topSec_add M m m')).trans
      (TensorProduct.add_tmul _ _ _)
  exact (congrArg _ h1).trans (toTS_add M N _ _)

/-- `topTmul` is additive in its right argument. -/
lemma topTmul_add_right (m : M) (n n' : N) :
    topTmul M N m (n + n') = topTmul M N m n + topTmul M N m n' := by
  have h1 : topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N (n + n')
      = (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n)
        + (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] topSec N n') :=
    (congrArg (topSec M m ⊗ₜ[(Spec R).presheaf.obj (op ⊤)] ·) (topSec_add N n n')).trans
      (TensorProduct.tmul_add _ _ _)
  exact (congrArg _ h1).trans (toTS_add M N _ _)

/-- `topTmul`, retyped into Mathlib's global-sections module, where `R` acts. -/
def topTmulG (m : M) (n : N) : Γ(tildeTensor M N, ⊤) := topTmul M N m n

/-- `topTmulG` is `R`-linear in its left argument: the `cTop`-action is the `R`-action. -/
lemma topTmulG_smul_left (r : R) (m : M) (n : N) :
    topTmulG M N (r • m) n = r • topTmulG M N m n :=
  (topTmul_smul_left M N r m n).trans
    (Scheme.Modules.smul_Spec_def (M := tildeTensor M N) r (topTmulG M N m n)).symm

/-- `topTmulG` is `R`-linear in its right argument. -/
lemma topTmulG_smul_right (r : R) (m : M) (n : N) :
    topTmulG M N m (r • n) = r • topTmulG M N m n :=
  (topTmul_smul_right M N r m n).trans
    (Scheme.Modules.smul_Spec_def (M := tildeTensor M N) r (topTmulG M N m n)).symm

/-- **The canonical map on global sections** `M ⊗_R N ⟶ Γ(Spec R, M̃ ⊗ Ñ)`. -/
def topTensorMap : (M ⊗[R] N) →ₗ[R] Γ(tildeTensor M N, ⊤) :=
  TensorProduct.lift (LinearMap.mk₂ (R : Type u) (topTmulG M N)
    (topTmul_add_left M N) (topTmulG_smul_left M N)
    (topTmul_add_right M N) (topTmulG_smul_right M N))

@[simp] lemma topTensorMap_tmul (m : M) (n : N) :
    topTensorMap M N (m ⊗ₜ[R] n) = topTmulG M N m n := rfl

/-! ### The comparison morphism -/

/-- **The comparison morphism** `(M ⊗_R N)~ ⟶ M̃ ⊗ Ñ`, the adjoint transpose of `topTensorMap`
under `AlgebraicGeometry.tilde.adjunction`, written out as `tilde.map` of `topTensorMap` followed
by the counit `AlgebraicGeometry.Scheme.Modules.fromTildeΓ`. -/
def tildeTensorComparison :
    tilde (ModuleCat.of (R : Type u) (M ⊗[R] N)) ⟶ tildeTensor M N :=
  tilde.map (ModuleCat.ofHom (topTensorMap M N)) ≫
    Scheme.Modules.fromTildeΓ (tildeTensor M N)

/-- Elementwise form of `AlgebraicGeometry.tilde.toOpen_map_app`. -/
lemma toOpen_map_app_apply {A B : ModuleCat.{u} R} (f : A ⟶ B) (U : (Spec R).Opens) (a : A) :
    ((tilde.map f).val.app (op U)).hom ((tilde.toOpen A U).hom a)
      = (tilde.toOpen B U).hom (f.hom a) :=
  congrArg (fun h => (ModuleCat.Hom.hom h) a) (tilde.toOpen_map_app f U)

/-- Elementwise form of `AlgebraicGeometry.Scheme.Modules.toOpen_fromTildeΓ_app`. -/
lemma toOpen_fromTildeΓ_app_apply (F : (Spec R).Modules) (U : (Spec R).Opens) (z : Γ(F, ⊤)) :
    ((modulesSpecToSheaf.map (Scheme.Modules.fromTildeΓ F)).hom.app (op U)).hom
        ((tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (op ⊤)) U).hom z)
      = ((modulesSpecToSheaf.obj F).obj.map (homOfLE (le_top : U ≤ ⊤)).op).hom z := by
  have h0 := Scheme.Modules.toOpen_fromTildeΓ_app F U
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h0) z

/-- At `U = ⊤` the restriction appearing in `toOpen_fromTildeΓ_app_apply` is the identity, so the
counit undoes `toOpen`. -/
lemma toOpen_fromTildeΓ_app_top (F : (Spec R).Modules) (z : Γ(F, ⊤)) :
    ((Scheme.Modules.fromTildeΓ F).val.app (op ⊤)).hom
        ((tilde.toOpen ((modulesSpecToSheaf.obj F).presheaf.obj (op ⊤)) ⊤).hom z) = z := by
  refine (toOpen_fromTildeΓ_app_apply F ⊤ z).trans ?_
  have h : (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : (Spec R).Opens)) := rfl
  rw [h, CategoryTheory.Functor.map_id]
  rfl

/-- **The comparison morphism on global sections** is `topTensorMap`. -/
lemma tildeTensorComparison_app_top (z : (M ⊗[R] N)) :
    ((tildeTensorComparison M N).val.app (op ⊤)).hom
        (topSec (ModuleCat.of (R : Type u) (M ⊗[R] N)) z)
      = topTensorMap M N z := by
  have h1 := toOpen_map_app_apply (ModuleCat.ofHom (topTensorMap M N)) (⊤ : (Spec R).Opens) z
  have h2 := toOpen_fromTildeΓ_app_top (tildeTensor M N) (topTensorMap M N z)
  exact (congrArg
    (fun y => (ModuleCat.Hom.hom
      ((Scheme.Modules.fromTildeΓ (tildeTensor M N)).val.app (op ⊤))) y) h1).trans h2

/-! ### The comparison morphism on stalks -/

section Stalk

variable (q : ((Spec R).toRingedSpace.carrier : Type u))

/-- The point, at Mathlib's spelling of the carrier of `Spec R`.  The two types are `rfl`-equal;
this retyping is what lets Mathlib's `tilde` instances be found. -/
abbrev pt : PrimeSpectrum.Top R := q

/-- Mathlib's `R`-module structure on the stalk of `Ã`, seated at the Tag 01CB spelling. -/
instance moduleRStalk (A : ModuleCat.{u} R) :
    Module (R : Type u) (grpStalk (Spec R).toRingedSpace (tildeSheaf A).val q) :=
  inferInstanceAs (Module (R : Type u) ((tilde A).presheaf.stalk (pt q)))

/-- `AlgebraicGeometry.tilde.toStalk`, retyped at the Tag 01CB spelling of the stalk, so that the
Tag 01CB stalk machinery and Mathlib's `IsLocalizedModule` instance speak about the same term. -/
def toStalkL (A : ModuleCat.{u} R) :
    A →ₗ[R] grpStalk (Spec R).toRingedSpace (tildeSheaf A).val q :=
  (tilde.toStalk A q).hom

/-- **The stalk of `Ã` at `q` is the localization of `A` at `q`**, seated at the Tag 01CB
spelling.  This is Mathlib's instance on `AlgebraicGeometry.tilde.toStalk`. -/
instance isLocalizedModule_toStalkL (A : ModuleCat.{u} R) :
    IsLocalizedModule (pt q).asIdeal.primeCompl (toStalkL q A) :=
  inferInstanceAs (IsLocalizedModule (pt q).asIdeal.primeCompl (tilde.toStalk A (pt q)).hom)

/-- The structure-sheaf stalk as an `R`-algebra, seated at the Tag 01CB spelling.  This is
`AlgebraicGeometry.StructureSheaf.stalkAlgebra`. -/
instance algRStalk : Algebra (R : Type u) (ringStalk (Spec R).toRingedSpace q) :=
  inferInstanceAs (Algebra (R : Type u)
    ((Spec.structureSheaf (R : Type u)).presheaf.stalk (pt q)))

/-- **The structure-sheaf stalk is the localization of `R` at the prime**, seated at the Tag 01CB
spelling.  This is `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`. -/
instance isLocRStalk :
    IsLocalization.AtPrime (ringStalk (Spec R).toRingedSpace q) (pt q).asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime
    ((Spec.structureSheaf (R : Type u)).presheaf.stalk (pt q)) (pt q).asIdeal)

/-- **The `R`-action on the stalk of `Ã` is the restriction of the `𝒪_{Spec R, q}`-action.**
Mathlib proves this for the `PresheafOfModules` stalk module structure;
`stalkModule_eq_presheafModule` carries it to the Tag 01CB one, which is what
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is stated over. -/
instance towerStalk (A : ModuleCat.{u} R) :
    IsScalarTower (R : Type u) (ringStalk (Spec R).toRingedSpace q)
      (grpStalk (Spec R).toRingedSpace (tildeSheaf A).val q) :=
  tower_transport (stalkModule_eq_presheafModule (X := Spec R) (tildeSheaf A).val q)
    (inferInstanceAs (IsScalarTower (R : Type u)
      ((structurePresheafInCommRingCat (R : Type u)).stalk (pt q))
      (TopCat.Presheaf.stalk (C := Ab.{u}) (moduleStructurePresheaf (R : Type u) A).presheaf
        (pt q))))

/-- `toStalkL` is the germ at `⊤` of the canonical global section. -/
lemma toStalkL_eq_grpGerm (A : ModuleCat.{u} R) (a : A) :
    toStalkL q A a
      = grpGerm (Spec R).toRingedSpace (tildeSheaf A).val q ⊤ (by trivial) (topSec A a) := rfl

/-- **The stalk map of the comparison morphism, on the image of `toStalk`.**  It carries the image
of `z : M ⊗_R N` to the germ of `topTensorMap z`. -/
lemma tildeTensorComparison_stalkMapL_toStalk (z : (M ⊗[R] N)) :
    stalkMapL (Spec R).toRingedSpace
        (tildeSheaf (ModuleCat.of (R : Type u) (M ⊗[R] N))).val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N)))).val
        (tildeTensorComparison M N).val q
        ((tilde.toStalk (ModuleCat.of (R : Type u) (M ⊗[R] N)) q).hom z)
      = grpGerm (Spec R).toRingedSpace
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N)))).val q ⊤
          (by trivial) (topTensorMap M N z) :=
  (Stacks.SheafOfModules.stalkMapL_germ (Spec R).toRingedSpace
      (tildeTensorComparison M N).val q ⊤ (by trivial)
      (topSec (ModuleCat.of (R : Type u) (M ⊗[R] N)) z)).trans
    (congrArg
      (fun y => grpGerm (Spec R).toRingedSpace
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N)))).val q ⊤ (by trivial) y)
      (tildeTensorComparison_app_top M N z))

/-- **The germ characterisation of the comparison morphism.**  Composed with the Tag 01CB
identification `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` of the stalk of a
  tensor product, the stalk map of
the comparison morphism carries `toStalk (m ⊗ n)` to `toStalk m ⊗ toStalk n`.

This is the statement an `IsLocalizedModule` argument needs: both sides of the comparison are
localizations of `M ⊗_R N` at `q`, and this pins the map between them on a generating set. -/
lemma tensorStalkIso_stalkMapL_toStalkL (m : M) (n : N) :
    tensorStalkIso (Spec R).toRingedSpace q (tildeSheaf M) (tildeSheaf N)
        (stalkMapL (Spec R).toRingedSpace
          (tildeSheaf (ModuleCat.of (R : Type u) (M ⊗[R] N))).val
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N)))).val
          (tildeTensorComparison M N).val q
          (toStalkL q (ModuleCat.of (R : Type u) (M ⊗[R] N)) (m ⊗ₜ[R] n)))
      = toStalkL q M m ⊗ₜ[ringStalk (Spec R).toRingedSpace q] toStalkL q N n :=
  (congrArg (tensorStalkIso (Spec R).toRingedSpace q (tildeSheaf M) (tildeSheaf N))
      (tildeTensorComparison_stalkMapL_toStalk M N q (m ⊗ₜ[R] n))).trans
    (tensorStalkIso_germ (Spec R).toRingedSpace q (tildeSheaf M) (tildeSheaf N) ⊤ (by trivial)
      (topSec M m) (topSec N n))

/-! ### Invertibility on stalks -/

/-- The stalk map of the comparison morphism, read in the tensor product of the two stalks over
`R` rather than over `𝒪_{Spec R, q}`.  The conversion is `IsLocalization.moduleTensorEquiv`,
which applies because the structure-sheaf stalk is a localization of `R` (`isLocRStalk`) and the
two actions on each stalk are compatible (`towerStalk`). -/
def stalkComparisonR :
    grpStalk (Spec R).toRingedSpace
        (tildeSheaf (ModuleCat.of (R : Type u) (M ⊗[R] N))).val q →ₗ[R]
      (grpStalk (Spec R).toRingedSpace (tildeSheaf M).val q ⊗[R]
        grpStalk (Spec R).toRingedSpace (tildeSheaf N).val q) :=
  LinearMap.restrictScalars (R : Type u)
    ((IsLocalization.moduleTensorEquiv (pt q).asIdeal.primeCompl
          (ringStalk (Spec R).toRingedSpace q)
          (grpStalk (Spec R).toRingedSpace (tildeSheaf M).val q)
          (grpStalk (Spec R).toRingedSpace (tildeSheaf N).val q)).toLinearMap ∘ₗ
      @LinearEquiv.toLinearMap _ _ _ _ _ _ _ _ _ _ _ _
          (stalkModule (Spec R).toRingedSpace (tildeTensor M N).val q) _
          (tensorStalkIso (Spec R).toRingedSpace q (tildeSheaf M) (tildeSheaf N)) ∘ₗ
        stalkMapL (Spec R).toRingedSpace
          (tildeSheaf (ModuleCat.of (R : Type u) (M ⊗[R] N))).val
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N)))).val
          (tildeTensorComparison M N).val q)

/-- `stalkComparisonR` on the image under `toStalk` of a pure tensor. -/
lemma stalkComparisonR_toStalkL (m : M) (n : N) :
    stalkComparisonR M N q (toStalkL q (ModuleCat.of (R : Type u) (M ⊗[R] N)) (m ⊗ₜ[R] n))
      = toStalkL q M m ⊗ₜ[R] toStalkL q N n :=
  congrArg
    (IsLocalization.moduleTensorEquiv (pt q).asIdeal.primeCompl
      (ringStalk (Spec R).toRingedSpace q)
      (grpStalk (Spec R).toRingedSpace (tildeSheaf M).val q)
      (grpStalk (Spec R).toRingedSpace (tildeSheaf N).val q))
    (tensorStalkIso_stalkMapL_toStalkL M N q m n)

/-- **`stalkComparisonR` commutes with the two localization maps**: precomposed with `toStalk` it
is `TensorProduct.map` of the two localization maps. -/
lemma stalkComparisonR_comp :
    stalkComparisonR M N q ∘ₗ toStalkL q (ModuleCat.of (R : Type u) (M ⊗[R] N))
      = TensorProduct.map (toStalkL q M) (toStalkL q N) :=
  TensorProduct.ext' (stalkComparisonR_toStalkL M N q)

/-- **`M_q ⊗_R N_q` is a localization of `M ⊗_R N` at `q`**, via the composite.  This is
Mathlib's `IsLocalization` instance for `TensorProduct.map` of two localization maps, transported
along `stalkComparisonR_comp`. -/
instance isLocalizedModule_stalkComparisonR_comp :
    IsLocalizedModule (pt q).asIdeal.primeCompl
      (stalkComparisonR M N q ∘ₗ toStalkL q (ModuleCat.of (R : Type u) (M ⊗[R] N))) := by
  rw [stalkComparisonR_comp]
  infer_instance

/-- **`stalkComparisonR` is bijective.**  It is a map between two localizations of `M ⊗_R N` at
`q` commuting with the localization maps. -/
lemma bijective_stalkComparisonR : Function.Bijective (stalkComparisonR M N q) := by
  have h : IsIso (ModuleCat.ofHom (stalkComparisonR M N q)) :=
    ModuleCat.isIso_of_isLocalizedModule_comp
      (S := (pt q).asIdeal.primeCompl)
      (f₁ := ModuleCat.ofHom (toStalkL q (ModuleCat.of (R : Type u) (M ⊗[R] N))))
      (isLocalizedModule_toStalkL q (ModuleCat.of (R : Type u) (M ⊗[R] N)))
      (isLocalizedModule_stalkComparisonR_comp M N q)
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- **The stalk map of the comparison morphism is bijective**, since the two identifications
composed onto it in `stalkComparisonR` are. -/
lemma bijective_stalkMapL_tildeTensorComparison :
    Function.Bijective
      (stalkMapL (Spec R).toRingedSpace
        (tildeSheaf (ModuleCat.of (R : Type u) (M ⊗[R] N))).val
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N)))).val
        (tildeTensorComparison M N).val q) := by
  exact (Function.Bijective.of_comp_iff' ((IsLocalization.moduleTensorEquiv
    (pt q).asIdeal.primeCompl (ringStalk (Spec R).toRingedSpace q) _ _).bijective.comp
      (tensorStalkIso (Spec R).toRingedSpace q (tildeSheaf M) (tildeSheaf N)).bijective) _).mp
    (bijective_stalkComparisonR M N q)

end Stalk

/-! ### The tensor half of Stacks 01I8 -/

/-- **The tensor half of Stacks 01I8.**  The comparison morphism
`(M ⊗_R N)~ ⟶ M̃ ⊗_{𝒪_{Spec R}} Ñ` is an isomorphism: it is bijective on every stalk by
`bijective_stalkMapL_tildeTensorComparison`, and a morphism of sheaves of modules which is an
isomorphism on every stalk is an isomorphism. -/
theorem isIso_tildeTensorComparison : IsIso (tildeTensorComparison M N) := by
  have h : IsIso (show tildeSheaf (ModuleCat.of (R : Type u) (M ⊗[R] N)) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tildeSheaf M))).obj ((tildeSheaf N))) from
      tildeTensorComparison M N) := by
    refine ExtensionByZeroModules.isIso_of_stalk_isIso
      (structureSheafRing (Spec R).toRingedSpace) _ fun x => ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_stalkMapL_tildeTensorComparison M N x
  exact h

/-- **The tensor half of Stacks 01I8, as an isomorphism**: the associated sheaf of a tensor
product of modules is the tensor product of the associated sheaves. -/
def tildeTensorIso :
    tilde (ModuleCat.of (R : Type u) (M ⊗[R] N)) ≅ tildeTensor M N :=
  @asIso _ _ _ _ (tildeTensorComparison M N) (isIso_tildeTensorComparison M N)

@[simp] lemma tildeTensorIso_hom :
    (tildeTensorIso M N).hom = tildeTensorComparison M N := rfl

end AlgebraicGeometry.TildeTensor

end
