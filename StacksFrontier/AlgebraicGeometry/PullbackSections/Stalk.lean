module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The sections of a quasi-coherent pullback to the spectrum of a stalk are the stalk

Let `ℱ` be a quasi-coherent `𝒪_Y`-module and `y` a point of `Y`. The canonical morphism
`Spec 𝒪_{Y,y} ⟶ Y` lies over every open neighbourhood of `y`, so a section of `ℱ` over an open
`U ∋ y` can be pulled back to a global section of `(Y.fromSpecStalk y)^* ℱ`, and

  `Γ(Spec 𝒪_{Y,y}, (Y.fromSpecStalk y)^* ℱ) ≅ ℱ_y`

as `𝒪_{Y,y}`-modules, the comparison carrying the pullback of a section to its germ at `y`.

For an affine open `U ∋ y`, both sides are the localisation of `Γ(ℱ, U)` at the prime of
`Γ(Y, U)` corresponding to `y`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackSectionsModule`: `Γ(f^*F, V)` as a `Γ(X, U)`-module,
  scalars acting through `AlgebraicGeometry.Scheme.Hom.appLE`.
* `AlgebraicGeometry.Scheme.Modules.pullbackSectionₗ`: pulling a section back,
  `Γ(F, U) → Γ(f^*F, V)`, as a `Γ(X, U)`-linear map.
* `AlgebraicGeometry.fromSpecStalkPullbackModule`: `Γ((Y.fromSpecStalk y)^* ℱ, ⊤)` as an
  `𝒪_{Y,y}`-module, scalars acting through `AlgebraicGeometry.Scheme.ΓSpecIso`.
* `AlgebraicGeometry.fromSpecStalkSectionsStalkEquiv`: **the comparison**
  `Γ(Spec 𝒪_{Y,y}, (Y.fromSpecStalk y)^* ℱ) ≃ₗ[𝒪_{Y,y}] ℱ_y`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_pullbackSectionₗ`: for `U` and `V` affine
  with `V ⊆ f⁻¹U`, if `Γ(Z, V)` is the localisation of `Γ(X, U)` at a submonoid `S` then
  `Γ(f^*F, V)` is the localisation of `Γ(F, U)` at `S`, through the pullback of sections.
* `AlgebraicGeometry.fromSpecStalk_appLE_top`: the map on sections of `Spec 𝒪_{Y,y} ⟶ Y` from `U`
  to the whole of `Spec 𝒪_{Y,y}` is the germ map followed by `Scheme.ΓSpecIso`.
* `AlgebraicGeometry.isLocalization_sections_fromSpecStalk`: `Γ(Spec 𝒪_{Y,y}, ⊤)` is the
  localisation of `Γ(Y, U)` at the prime corresponding to `y`.
* `AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv`: **the comparison together with
  its normalisation.** There is an `𝒪_{Y,y}`-linear isomorphism
  `Γ(Spec 𝒪_{Y,y}, (Y.fromSpecStalk y)^* ℱ) ≅ ℱ_y` sending the pullback of a section of `ℱ` over
  an affine neighbourhood of `y` to its germ at `y`.

## Implementation notes

`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` is made locally irreducible. Its source is
a tensor product whose `Module Γ(X, U) Γ(Z, V)` instance is `Module.compHom`, while the tensor
product `Γ(Z, V) ⊗ Γ(F, U)` written with the algebra structure of
`AlgebraicGeometry.Scheme.Hom.appLE` carries `Algebra.toModule`; the two are definitionally equal,
but identifying `1 ⊗ₜ a` across that boundary inside an application of the comparison unfolds the
comparison and exhausts the recursion budget unless the comparison is opaque.

The module structures on `Γ(f^*F, V)` and on the stalk are supplied explicitly throughout:
typeclass resolution does not find a module structure on the stalk of an `X.Modules` over the
stalk of the structure sheaf.

`AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv` states the comparison and its
normalisation together, as an existential, rather than as a definition plus a `simp` lemma: the
type of `AlgebraicGeometry.fromSpecStalkSectionsStalkEquiv` carries the two module structures as
`let`s, and a `let`-headed function type is not seen through by the coercion to a function, so that
definition cannot be applied to an argument inside a statement.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01HX](https://stacks.math.columbia.edu/tag/01HX)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

attribute [local irreducible] affinePullbackSectionsBaseChangeIso

/-- The sections of a pullback over an open `V`, as a module over the functions on an open `U` of
the target with `V ⊆ f⁻¹U`: scalars act through `AlgebraicGeometry.Scheme.Hom.appLE`. -/
@[instance_reducible]
public noncomputable def Scheme.Modules.pullbackSectionsModule {X Z : Scheme.{u}} (f : Z ⟶ X)
    (F : X.Modules) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    Module Γ(X, U) Γ((Scheme.Modules.pullback f).obj F, V) :=
  Module.compHom _ (f.appLE U V h).hom

/-- **Pulling a section back is linear.** `AlgebraicGeometry.Scheme.Modules.pullbackSection`, read
as a `Γ(X, U)`-linear map `Γ(F, U) → Γ(f^*F, V)` for the module structure of
`AlgebraicGeometry.Scheme.Modules.pullbackSectionsModule`. -/
public noncomputable def Scheme.Modules.pullbackSectionₗ {X Z : Scheme.{u}} (f : Z ⟶ X)
    (F : X.Modules) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    letI := Scheme.Modules.pullbackSectionsModule f F U V h
    Γ(F, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj F, V) :=
  letI := Scheme.Modules.pullbackSectionsModule f F U V h
  { toFun := Scheme.Modules.pullbackSection f F U V h
    map_add' := fun a b => by
      have h1 : ∀ y w : Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U),
          (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op (y + w)
              : Γ((Scheme.Modules.pullback f).obj F, V)) =
            (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op y
                : Γ((Scheme.Modules.pullback f).obj F, V)) +
              (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op w
                : Γ((Scheme.Modules.pullback f).obj F, V)) := fun y w => map_add _ y w
      have hpa : ∀ z w : Γ((Scheme.Modules.pushforward f).obj
            ((Scheme.Modules.pullback f).obj F), U),
          (z + w) = @HAdd.hAdd Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U)
            Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U)
            Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U) _ z w :=
        fun _ _ => rfl
      change (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app U (a + b))
          : Γ((Scheme.Modules.pullback f).obj F, V)) = _
      rw [map_add, hpa]
      exact h1 _ _
    map_smul' := fun r a => by
      have h2 : ∀ y : Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U),
          (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op ((f.app U r) • y)
              : Γ((Scheme.Modules.pullback f).obj F, V)) =
            (f.appLE U V h).hom r •
              (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op y
                : Γ((Scheme.Modules.pullback f).obj F, V)) := by
        intro y
        rw [Scheme.Modules.map_smul]
        rfl
      have hps : ∀ z : Γ((Scheme.Modules.pushforward f).obj
            ((Scheme.Modules.pullback f).obj F), U),
          (r • z) = @HSMul.hSMul Γ(Z, f ⁻¹ᵁ U)
            Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U)
            Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U) _ (f.app U r) z :=
        fun _ => rfl
      change (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app U (r • a))
          : Γ((Scheme.Modules.pullback f).obj F, V)) = _
      rw [Scheme.Modules.Hom.app_smul, hps]
      exact h2 _ }

/-- `AlgebraicGeometry.Scheme.Modules.pullbackSectionₗ` is
`AlgebraicGeometry.Scheme.Modules.pullbackSection`. -/
@[simp] public theorem Scheme.Modules.pullbackSectionₗ_apply {X Z : Scheme.{u}} (f : Z ⟶ X)
    (F : X.Modules) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : Γ(F, U)) :
    letI := Scheme.Modules.pullbackSectionsModule f F U V h
    Scheme.Modules.pullbackSectionₗ f F U V h a =
      Scheme.Modules.pullbackSection f F U V h a := rfl

/-- **The sections of a quasi-coherent pullback are a localisation of the sections.** For `U ⊆ X`
and `V ⊆ Z` affine with `V ⊆ f⁻¹U` and `F` quasi-coherent, if `Γ(Z, V)` is the localisation of
`Γ(X, U)` at a submonoid `S`, then pulling sections back exhibits `Γ(f^*F, V)` as the localisation
of `Γ(F, U)` at `S`. -/
public theorem Scheme.Modules.isLocalizedModule_pullbackSectionₗ {X Z : Scheme.{u}} (f : Z ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Z.Opens}
    (hV : IsAffineOpen V) (h : V ≤ f ⁻¹ᵁ U) (S : Submonoid Γ(X, U))
    (hS : letI : Algebra Γ(X, U) Γ(Z, V) := (f.appLE U V h).hom.toAlgebra
      IsLocalization S Γ(Z, V)) :
    letI := Scheme.Modules.pullbackSectionsModule f F U V h
    IsLocalizedModule S (Scheme.Modules.pullbackSectionₗ f F U V h) := by
  let := Scheme.Modules.pullbackSectionsModule f F U V h
  let : Algebra Γ(X, U) Γ(Z, V) := (f.appLE U V h).hom.toAlgebra
  let : IsLocalization S Γ(Z, V) := hS
  have : IsScalarTower Γ(X, U) Γ(Z, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
    ⟨fun r b n => mul_smul ((f.appLE U V h).hom r) b n⟩
  let e : (TensorProduct Γ(X, U) Γ(Z, V) Γ(F, U)) ≃ₗ[Γ(Z, V)]
      Γ((Scheme.Modules.pullback f).obj F, V) :=
    (affinePullbackSectionsBaseChangeIso f F hU hV h).toLinearEquiv
  have heq : Scheme.Modules.pullbackSectionₗ f F U V h =
      (e.restrictScalars Γ(X, U)).toLinearMap ∘ₗ
        TensorProduct.mk Γ(X, U) Γ(Z, V) Γ(F, U) 1 := by
    refine LinearMap.ext fun c => ?_
    rw [LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, Scheme.Modules.pullbackSectionₗ_apply]
    exact (affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV h c).symm
  rw [heq]
  exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk Γ(X, U) Γ(Z, V) Γ(F, U) 1)
    (e.restrictScalars Γ(X, U))

/-! ### The spectrum of a stalk -/

/-- **The whole of `Spec 𝒪_{Y,y}` lies over every open neighbourhood of `y`.** The range of
`Spec 𝒪_{Y,y} ⟶ Y` is the set of points specialising to `y`. -/
public theorem le_preimage_fromSpecStalk_of_mem {Y : Scheme.{u}} (y : Y) (U : Y.Opens)
    (hy : y ∈ U) :
    (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ≤ Y.fromSpecStalk y ⁻¹ᵁ U := by
  intro p _
  have hmem : (Y.fromSpecStalk y).base p ∈ Set.range (Y.fromSpecStalk y).base := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hmem
  exact hmem.mem_open U.isOpen hy

/-- **The map on sections of `Spec 𝒪_{Y,y} ⟶ Y`, from an open neighbourhood of `y` to the whole of
`Spec 𝒪_{Y,y}`, is the germ map at `y`** followed by the identification of `𝒪_{Y,y}` with the
global functions on its spectrum. -/
public theorem fromSpecStalk_appLE_top {Y : Scheme.{u}} (y : Y) {U : Y.Opens} (hy : y ∈ U) :
    (Y.fromSpecStalk y).appLE U ⊤ (le_preimage_fromSpecStalk_of_mem y U hy) =
      Y.presheaf.germ U y hy ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [show ((homOfLE le_top : (Y.fromSpecStalk y) ⁻¹ᵁ U ⟶ ⊤)).op ≫
      (homOfLE (le_preimage_fromSpecStalk_of_mem y U hy)).op
      = (𝟙 (op (⊤ : (Spec (Y.presheaf.stalk y)).Opens))) from Subsingleton.elim _ _]
  simp

/-- `AlgebraicGeometry.fromSpecStalk_appLE_top` read on an element. -/
public theorem fromSpecStalk_appLE_top_apply {Y : Scheme.{u}} (y : Y) {U : Y.Opens} (hy : y ∈ U)
    (r : Γ(Y, U)) :
    ((Y.fromSpecStalk y).appLE U ⊤ (le_preimage_fromSpecStalk_of_mem y U hy)).hom r =
      (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom ((Y.presheaf.germ U y hy).hom r) :=
  (ConcreteCategory.congr_hom (fromSpecStalk_appLE_top y hy) r).trans
    (CommRingCat.comp_apply _ _ r)

/-- **The global functions on `Spec 𝒪_{Y,y}` are the localisation of the functions on an affine
neighbourhood of `y` at the prime of `y`.** -/
public theorem isLocalization_sections_fromSpecStalk {Y : Scheme.{u}} (y : Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (hy : y ∈ U) :
    letI : Algebra Γ(Y, U) Γ(Spec (Y.presheaf.stalk y), ⊤) :=
      ((Y.fromSpecStalk y).appLE U ⊤ (le_preimage_fromSpecStalk_of_mem y U hy)).hom.toAlgebra
    IsLocalization (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      Γ(Spec (Y.presheaf.stalk y), ⊤) := by
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) := (Y.presheaf.germ U y hy).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(Spec (Y.presheaf.stalk y), ⊤) :=
    ((Y.fromSpecStalk y).appLE U ⊤ (le_preimage_fromSpecStalk_of_mem y U hy)).hom.toAlgebra
  let : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact (IsLocalization.isLocalization_iff_of_algEquiv _
    (AlgEquiv.ofRingEquiv
      (f := (Scheme.ΓSpecIso (Y.presheaf.stalk y)).symm.commRingCatIsoToRingEquiv)
      fun r => (fromSpecStalk_appLE_top_apply y hy r).symm)).mp inferInstance

/-- The global sections of the pullback of `ℱ` to `Spec 𝒪_{Y,y}`, as an `𝒪_{Y,y}`-module: scalars
act through the identification of `𝒪_{Y,y}` with the global functions on its spectrum. -/
@[instance_reducible]
public noncomputable def fromSpecStalkPullbackModule {Y : Scheme.{u}} (ℱ : Y.Modules) (y : Y) :
    Module (Y.presheaf.stalk y)
      Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj ℱ, ⊤) :=
  Module.compHom _ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom

/-- **The global sections of the pullback of a quasi-coherent module to the spectrum of a stalk are
the stalk.** The `𝒪_{Y,y}`-linear isomorphism
`Γ(Spec 𝒪_{Y,y}, (Y.fromSpecStalk y)^* ℱ) ≃ ℱ_y` identifying both sides with the localisation of
`Γ(ℱ, U)`, for an affine open `U ∋ y`, at the prime of `Γ(Y, U)` corresponding to `y`. -/
public noncomputable def fromSpecStalkSectionsStalkEquiv {Y : Scheme.{u}} (ℱ : Y.Modules)
    [ℱ.IsQuasicoherent] (y : Y) {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U) :
    letI := fromSpecStalkPullbackModule ℱ y
    letI : Module (Y.presheaf.stalk y) (ℱ.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ℱ.val y
    Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj ℱ, ⊤) ≃ₗ[Y.presheaf.stalk y]
      ℱ.presheaf.stalk y := by
  letI := fromSpecStalkPullbackModule ℱ y
  letI : Module (Y.presheaf.stalk y) (ℱ.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) ℱ.val y
  letI := Scheme.Modules.pullbackSectionsModule (Y.fromSpecStalk y) ℱ U ⊤
    (le_preimage_fromSpecStalk_of_mem y U hy)
  letI := affineStalkModule ℱ U y hy
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := (Y.presheaf.germ U y hy).hom.toAlgebra
  letI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  haveI := Scheme.Modules.isLocalizedModule_pullbackSectionₗ (Y.fromSpecStalk y) ℱ hU
    (isAffineOpen_top (Spec (Y.presheaf.stalk y))) (le_preimage_fromSpecStalk_of_mem y U hy)
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (isLocalization_sections_fromSpecStalk y hU hy)
  haveI := affineGerm_isLocalized ℱ U hU y hy
  haveI : IsScalarTower Γ(Y, U) (Y.presheaf.stalk y)
      Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj ℱ, ⊤) := by
    refine ⟨fun r a n => ?_⟩
    change (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
        ((Y.presheaf.germ U y hy).hom r * a) • n =
      ((Y.fromSpecStalk y).appLE U ⊤ (le_preimage_fromSpecStalk_of_mem y U hy)).hom r •
        ((Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom a • n)
    rw [map_mul, mul_smul, fromSpecStalk_appLE_top_apply]
  haveI : IsScalarTower Γ(Y, U) (Y.presheaf.stalk y) (ℱ.presheaf.stalk y) :=
    ⟨fun r a z => mul_smul ((Y.presheaf.germ U y hy).hom r) a z⟩
  exact (IsLocalizedModule.linearEquiv (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (Scheme.Modules.pullbackSectionₗ (Y.fromSpecStalk y) ℱ U ⊤
      (le_preimage_fromSpecStalk_of_mem y U hy))
    (affineGerm ℱ U y hy)).extendScalarsOfIsLocalization
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)

/-- **The comparison of the sections of the pullback with the stalk, together with its
normalisation.** There is an `𝒪_{Y,y}`-linear isomorphism

  `Γ(Spec 𝒪_{Y,y}, (Y.fromSpecStalk y)^* ℱ) ≅ ℱ_y`

carrying the pullback of a section of `ℱ` over an affine open `U ∋ y` to its germ at `y`. -/
public theorem exists_fromSpecStalkSectionsStalkLinearEquiv {Y : Scheme.{u}} (ℱ : Y.Modules)
    [ℱ.IsQuasicoherent] (y : Y) {U : Y.Opens} (hU : IsAffineOpen U) (hy : y ∈ U) :
    letI := fromSpecStalkPullbackModule ℱ y
    letI : Module (Y.presheaf.stalk y) (ℱ.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ℱ.val y
    letI := Scheme.Modules.pullbackSectionsModule (Y.fromSpecStalk y) ℱ U ⊤
      (le_preimage_fromSpecStalk_of_mem y U hy)
    ∃ e : Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj ℱ, ⊤) ≃ₗ[Y.presheaf.stalk y]
        ℱ.presheaf.stalk y,
      ∀ a : Γ(ℱ, U), e (Scheme.Modules.pullbackSectionₗ (Y.fromSpecStalk y) ℱ U ⊤
        (le_preimage_fromSpecStalk_of_mem y U hy) a) = ℱ.presheaf.germ U y hy a := by
  refine ⟨fromSpecStalkSectionsStalkEquiv ℱ y hU hy, fun a => ?_⟩
  let := fromSpecStalkPullbackModule ℱ y
  let := Scheme.Modules.pullbackSectionsModule (Y.fromSpecStalk y) ℱ U ⊤
    (le_preimage_fromSpecStalk_of_mem y U hy)
  let := affineStalkModule ℱ U y hy
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) := (Y.presheaf.germ U y hy).hom.toAlgebra
  let : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  have := Scheme.Modules.isLocalizedModule_pullbackSectionₗ (Y.fromSpecStalk y) ℱ hU
    (isAffineOpen_top (Spec (Y.presheaf.stalk y))) (le_preimage_fromSpecStalk_of_mem y U hy)
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (isLocalization_sections_fromSpecStalk y hU hy)
  have := affineGerm_isLocalized ℱ U hU y hy
  exact IsLocalizedModule.linearEquiv_apply (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (Scheme.Modules.pullbackSectionₗ (Y.fromSpecStalk y) ℱ U ⊤
      (le_preimage_fromSpecStalk_of_mem y U hy)) (affineGerm ℱ U y hy) a

end AlgebraicGeometry

end
