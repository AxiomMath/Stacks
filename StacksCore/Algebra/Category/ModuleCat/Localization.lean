module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Localization

/-! ## Equivalence of category of modules over localization -/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R] (S : Submonoid R)

open CategoryTheory

suppress_compilation

namespace ModuleCat

/-- Every `s ∈ S` acts invertibly. -/
def invertibleSMul : ObjectProperty (ModuleCat.{v} R) :=
  fun N => ∀ s : S, IsUnit (algebraMap R (Module.End R N) s)

lemma invertibleSMul_iff (N : ModuleCat.{v} R) :
    invertibleSMul S N ↔ ∀ s : S, IsUnit (algebraMap R (Module.End R N) s) :=
  Iff.rfl

/-- 07JY's functor: `localizedModuleFunctor` restricted to the subcategory. -/
@[implicit_reducible]
def localizedModuleFunctorInvertibleSMul [Small.{v, u} R] :
    (invertibleSMul S).FullSubcategory ⥤ ModuleCat.{v} (Localization S) :=
  (invertibleSMul S).ι ⋙ localizedModuleFunctor S

theorem invertibleSMul_of_isScalarTower (R₀ : Type*) [CommSemiring R₀] [Algebra R R₀]
    [IsLocalization S R₀] (N : Type*) [AddCommGroup N] [Module R N]
    [Module R₀ N] [IsScalarTower R R₀ N] (s : S) :
    IsUnit (algebraMap R (Module.End R N) s) := by
  rw [← (Algebra.lsmul R (A := R₀) R N).commutes]
  exact (IsLocalization.map_units R₀ s).map _

/-- The restricted `R`-action on a `Localization S`-module is the `algebraMap`-action,
so restriction of scalars along the localization map is a scalar tower. -/
instance (M : ModuleCat.{v} (Localization S)) :
    IsScalarTower R (Localization S) ((restrictScalars (algebraMap R (Localization S))).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- On a `Localization S`-module, every `s ∈ S` acts invertibly after restriction. -/
theorem invertibleSMul_restrictScalars (M : ModuleCat.{v} (Localization S)) :
    invertibleSMul S ((restrictScalars (algebraMap R (Localization S))).obj M) :=
  invertibleSMul_of_isScalarTower S (Localization S) _

/-- The quasi-inverse: restriction of scalars, corestricted to the subcategory. -/
@[implicit_reducible]
def restrictScalarsInvertibleSMul :
    ModuleCat.{v} (Localization S) ⥤ (invertibleSMul S).FullSubcategory :=
  ObjectProperty.lift _ (restrictScalars (algebraMap R (Localization S)))
    (invertibleSMul_restrictScalars S)

/-- The identity map as an `R`-linear equivalence between a module with its scalars
restricted along `algebraMap R A` and the same module with a compatible `R`-action:
the restricted action agrees with the given one by the scalar tower. -/
def restrictScalarsAlgebraMapEquiv {A : Type*} [CommRing A] [Algebra R A]
    (M : ModuleCat.{v} A) [Module R M] [IsScalarTower R A M] :
    ((restrictScalars (algebraMap R A)).obj M : Type v) ≃ₗ[R] M where
  __ := AddEquiv.refl _
  map_smul' r _ := algebraMap_smul A r _

@[simp] lemma restrictScalarsAlgebraMapEquiv_apply {A : Type*} [CommRing A] [Algebra R A]
    (M : ModuleCat.{v} A) [Module R M] [IsScalarTower R A M]
    (x : ((restrictScalars (algebraMap R A)).obj M : Type v)) :
    restrictScalarsAlgebraMapEquiv (R := R) M x = x := rfl

@[simp] lemma restrictScalarsAlgebraMapEquiv_symm_apply {A : Type*} [CommRing A] [Algebra R A]
    (M : ModuleCat.{v} A) [Module R M] [IsScalarTower R A M] (x : M) :
    (restrictScalarsAlgebraMapEquiv (R := R) M).symm x = x := rfl

/-- `restrictScalarsAlgebraMapEquiv` as an isomorphism in `ModuleCat R`. -/
def restrictScalarsAlgebraMapIso {A : Type*} [CommRing A] [Algebra R A]
    (M : ModuleCat.{v} A) [Module R M] [IsScalarTower R A M] :
    (restrictScalars (algebraMap R A)).obj M ≅ of R M :=
  LinearEquiv.toModuleIso (restrictScalarsAlgebraMapEquiv M)

/-- A module on which every `s ∈ S` acts invertibly is its own localization at `S`. -/
theorem isLocalizedModule_id_of_invertibleSMul (N : ModuleCat.{v} R)
    (hN : invertibleSMul S N) :
    IsLocalizedModule S (LinearMap.id : N →ₗ[R] N) where
  map_units := hN
  surj y := ⟨(y, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congr_arg _ h⟩

/-- The restriction of scalars of a `Localization S`-module is its own localization at `S`:
`S` already acts invertibly on it (`invertibleSMul_restrictScalars`). -/
instance (M : ModuleCat.{v} (Localization S)) :
    IsLocalizedModule S
      (LinearMap.id :
        ((restrictScalars (algebraMap R (Localization S))).obj M : Type v) →ₗ[R]
          ((restrictScalars (algebraMap R (Localization S))).obj M : Type v)) :=
  isLocalizedModule_id_of_invertibleSMul S
    ((restrictScalars (algebraMap R (Localization S))).obj M)
    (invertibleSMul_restrictScalars S M)

/-- `IsLocalizedModule.linearMap_ext`, restated over `[CommRing R]`.

`IsLocalizedModule.linearMap_ext` is stated over `[CommSemiring R]`, so applying it to a
goal elaborated over `[CommRing R]` produces a goal skeleton whose `Semiring R` instance is
spelled `CommSemiring.toSemiring (CommRing.toCommSemiring _)`, whereas every term elaborated
in a `CommRing`/`ModuleCat` context spells it `Ring.toSemiring (CommRing.toRing _)`.  The two
spellings are definitionally equal but not reducibly so, which prevents `simp` and `rw` from
matching any later lemma against the resulting mixed goal.  Restating the lemma in the
`CommRing` context keeps the whole proof state in a single spelling. -/
theorem isLocalizedModule_linearMap_ext {M M' N N' : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (f' : N →ₗ[R] N') [IsLocalizedModule S f']
    ⦃g g' : M' →ₗ[R] N'⦄ (h : g ∘ₗ f = g' ∘ₗ f) : g = g' :=
  IsLocalizedModule.linearMap_ext S f f' h

/-- Unit component: for `X` in the subcategory, restricting the localized module
recovers `X`, by uniqueness of localizations (`X` is its own localization).

The type is deliberately spelled with the *composite* functor, matching the components
required by `NatIso.ofComponents`, so that unit-related statements share one spelling of the
underlying `ModuleCat R` object. -/
def localizedModuleFunctorCompResIso [Small.{v, u} R]
    (X : (invertibleSMul S).FullSubcategory) :
    (localizedModuleFunctorInvertibleSMul S ⋙ restrictScalarsInvertibleSMul S).obj X ≅ X :=
  haveI := isLocalizedModule_id_of_invertibleSMul S X.obj X.property
  (invertibleSMul S).isoMk <|
    restrictScalarsAlgebraMapIso (X.obj.localizedModule S) ≪≫
      LinearEquiv.toModuleIso
        (IsLocalizedModule.linearEquiv S (X.obj.localizedModuleMkLinearMap S)
          (LinearMap.id : X.obj →ₗ[R] X.obj))

/-- The canonical localization map from `X` into the underlying `R`-module of
`(localizedModuleFunctorInvertibleSMul S ⋙ restrictScalarsInvertibleSMul S).obj X`.
Bundling it as a definition (rather than inlining the composite with
`restrictScalarsAlgebraMapEquiv`) pins the codomain to the composite-functor spelling used
by the unit isomorphism and its naturality statement. -/
noncomputable def unitMkLinearMap [Small.{v, u} R] (X : (invertibleSMul S).FullSubcategory) :
    X.obj →ₗ[R] ((localizedModuleFunctorInvertibleSMul S ⋙
      restrictScalarsInvertibleSMul S).obj X).obj :=
  (restrictScalarsAlgebraMapEquiv (X.obj.localizedModule S)).symm.toLinearMap ∘ₗ
    X.obj.localizedModuleMkLinearMap S

instance [Small.{v, u} R] (X : (invertibleSMul S).FullSubcategory) :
    IsLocalizedModule S (unitMkLinearMap S X) :=
  inferInstanceAs (IsLocalizedModule S
    ((restrictScalarsAlgebraMapEquiv (X.obj.localizedModule S)).symm.toLinearMap ∘ₗ
      X.obj.localizedModuleMkLinearMap S))

/-- `@[simps]`-style apply lemma: `localizedModuleFunctorInvertibleSMul ⋙
restrictScalarsInvertibleSMul` applied to `f` sends `unitMk x` to `unitMk (f x)`. -/
lemma localizedModuleFunctorCompRes_map_unitMkLinearMap [Small.{v, u} R]
    {X Y : (invertibleSMul S).FullSubcategory} (f : X ⟶ Y) (x : X.obj) :
    ((localizedModuleFunctorInvertibleSMul S ⋙ restrictScalarsInvertibleSMul S).map
        f).hom.hom (unitMkLinearMap S X x) =
      unitMkLinearMap S Y (f.hom.hom x) :=
  IsLocalizedModule.map_apply S (X.obj.localizedModuleMkLinearMap S)
    (Y.obj.localizedModuleMkLinearMap S) f.hom.hom x

/-- `@[simps]`-style apply lemma: the unit component of 07JY sends `unitMk x` to `x`. -/
lemma localizedModuleFunctorCompResIso_hom_unitMkLinearMap [Small.{v, u} R]
    (X : (invertibleSMul S).FullSubcategory) (x : X.obj) :
    (localizedModuleFunctorCompResIso S X).hom.hom.hom (unitMkLinearMap S X x) = x := by
  have := isLocalizedModule_id_of_invertibleSMul S X.obj X.property
  exact IsLocalizedModule.linearEquiv_apply S (X.obj.localizedModuleMkLinearMap S)
    (LinearMap.id : X.obj →ₗ[R] X.obj) x

lemma localizedModuleFunctorCompResIso_naturality [Small.{v, u} R]
    {X Y : (invertibleSMul S).FullSubcategory} (f : X ⟶ Y) :
    (localizedModuleFunctorInvertibleSMul S ⋙ restrictScalarsInvertibleSMul S).map f ≫
        (localizedModuleFunctorCompResIso S Y).hom =
      (localizedModuleFunctorCompResIso S X).hom ≫ f := by
  have := isLocalizedModule_id_of_invertibleSMul S Y.obj Y.property
  apply InducedCategory.Hom.ext
  apply ModuleCat.hom_ext
  apply isLocalizedModule_linearMap_ext S (unitMkLinearMap S X)
    (LinearMap.id : Y.obj →ₗ[R] Y.obj)
  ext x
  simp [-Functor.comp_map, -Functor.comp_obj, localizedModuleFunctorCompRes_map_unitMkLinearMap,
    localizedModuleFunctorCompResIso_hom_unitMkLinearMap]

/-- Counit component: localizing the restriction of a `Localization S`-module `M`
recovers `M`, since `id : (restrict M) →ₗ[R] M` is itself a localization map. -/
def resCompLocalizedModuleFunctorIso [Small.{v, u} R] (M : ModuleCat.{v} (Localization S)) :
    (restrictScalarsInvertibleSMul S ⋙ localizedModuleFunctorInvertibleSMul S).obj M ≅ M :=
  LinearEquiv.toModuleIso
    ((IsLocalizedModule.linearEquiv S
        (((restrictScalars (algebraMap R (Localization S))).obj M).localizedModuleMkLinearMap S)
        (LinearMap.id :
          ((restrictScalars (algebraMap R (Localization S))).obj M : Type v) →ₗ[R] _)
      ).extendScalarsOfIsLocalization S (Localization S))

/-- The `R`-module structure on the underlying type of `(restrictScalarsInvertibleSMul S ⋙
localizedModuleFunctorInvertibleSMul S).obj M`, given by the `R`-module structure on the
localized module.  Registered at the composite-functor spelling so that instance search
succeeds on the objects appearing in the counit naturality statement. -/
noncomputable instance [Small.{v, u} R] (M : ModuleCat.{v} (Localization S)) :
    Module R ((restrictScalarsInvertibleSMul S ⋙
      localizedModuleFunctorInvertibleSMul S).obj M : Type v) :=
  inferInstanceAs (Module R
    (((restrictScalars (algebraMap R (Localization S))).obj M).localizedModule S))

instance [Small.{v, u} R] (M : ModuleCat.{v} (Localization S)) :
    IsScalarTower R (Localization S) ((restrictScalarsInvertibleSMul S ⋙
      localizedModuleFunctorInvertibleSMul S).obj M : Type v) :=
  inferInstanceAs (IsScalarTower R (Localization S)
    (((restrictScalars (algebraMap R (Localization S))).obj M).localizedModule S))

/-- The canonical localization map from the restriction of scalars of `M` into the
underlying `R`-module of `(restrictScalarsInvertibleSMul S ⋙
localizedModuleFunctorInvertibleSMul S).obj M`.  Bundling it as a definition pins the
codomain to the composite-functor spelling used by the counit isomorphism and its
naturality statement. -/
noncomputable def counitMkLinearMap [Small.{v, u} R] (M : ModuleCat.{v} (Localization S)) :
    ((restrictScalars (algebraMap R (Localization S))).obj M : Type v) →ₗ[R]
    ((restrictScalarsInvertibleSMul S ⋙ localizedModuleFunctorInvertibleSMul S).obj M : Type v) :=
  ((restrictScalars (algebraMap R (Localization S))).obj M).localizedModuleMkLinearMap S

instance [Small.{v, u} R] (M : ModuleCat.{v} (Localization S)) :
    IsLocalizedModule S (counitMkLinearMap S M) :=
  inferInstanceAs (IsLocalizedModule S
    (((restrictScalars (algebraMap R (Localization S))).obj M).localizedModuleMkLinearMap S))

lemma restrictScalarsCompLocalizedModuleFunctor_map_counitMkLinearMap [Small.{v, u} R]
    {M N : ModuleCat.{v} (Localization S)} (g : M ⟶ N)
    (x : ((restrictScalars (algebraMap R (Localization S))).obj M : Type v)) :
    ((restrictScalarsInvertibleSMul S ⋙ localizedModuleFunctorInvertibleSMul S).map g).hom
        (counitMkLinearMap S M x) =
      counitMkLinearMap S N
        (((restrictScalars (algebraMap R (Localization S))).map g).hom x) :=
  IsLocalizedModule.map_apply S
    (((restrictScalars (algebraMap R (Localization S))).obj M).localizedModuleMkLinearMap S)
    (((restrictScalars (algebraMap R (Localization S))).obj N).localizedModuleMkLinearMap S)
    ((restrictScalars (algebraMap R (Localization S))).map g).hom x

lemma resCompLocalizedModuleFunctorIso_hom_counitMkLinearMap [Small.{v, u} R]
    (M : ModuleCat.{v} (Localization S))
    (x : ((restrictScalars (algebraMap R (Localization S))).obj M : Type v)) :
    (resCompLocalizedModuleFunctorIso S M).hom.hom (counitMkLinearMap S M x) = x :=
  IsLocalizedModule.linearEquiv_apply S
    (((restrictScalars (algebraMap R (Localization S))).obj M).localizedModuleMkLinearMap S)
    (LinearMap.id :
      ((restrictScalars (algebraMap R (Localization S))).obj M : Type v) →ₗ[R] _) x

@[simp]
lemma restrictScalars_algebraMap_map_hom_apply {M N : ModuleCat.{v} (Localization S)}
    (g : M ⟶ N) (x : ((restrictScalars (algebraMap R (Localization S))).obj M : Type v)) :
    ((restrictScalars (algebraMap R (Localization S))).map g).hom x = g.hom x := rfl

lemma resCompLocalizedModuleFunctor_hom_ext [Small.{v, u} R]
    {M Z : ModuleCat.{v} (Localization S)}
    {a b : (restrictScalarsInvertibleSMul S ⋙ localizedModuleFunctorInvertibleSMul S).obj M ⟶ Z}
    (h : ∀ x, a.hom (counitMkLinearMap S M x) = b.hom (counitMkLinearMap S M x)) : a = b := by
  let : Module R (Z : Type v) := Module.compHom Z (algebraMap R (Localization S))
  let : IsScalarTower R (Localization S) (Z : Type v) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule S (LinearMap.id (M := Z)) := isLocalizedModule_id S _ (Localization S)
  refine ModuleCat.hom_ext (LinearMap.restrictScalars_injective R <| isLocalizedModule_linearMap_ext
    S (counitMkLinearMap S M) LinearMap.id ?_)
  simpa [LinearMap.ext_iff] using h

lemma resCompLocalizedModuleFunctorIso_hom_naturality [Small.{v, u} R]
      {M N : ModuleCat.{v} (Localization S)} (g : M ⟶ N) :
      (restrictScalarsInvertibleSMul S ⋙ localizedModuleFunctorInvertibleSMul S).map g ≫
        (resCompLocalizedModuleFunctorIso S N).hom =
      (resCompLocalizedModuleFunctorIso S M).hom ≫ g := by
  apply resCompLocalizedModuleFunctor_hom_ext
  intro x
  -- Only the composition applications are unfolded: unfolding `Functor.comp_map` as well
  -- would destroy the `(res ⋙ locFun).map g` pattern the naturality lemma matches on.
  simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [restrictScalarsCompLocalizedModuleFunctor_map_counitMkLinearMap,
    resCompLocalizedModuleFunctorIso_hom_counitMkLinearMap,
    resCompLocalizedModuleFunctorIso_hom_counitMkLinearMap,
    restrictScalars_algebraMap_map_hom_apply]

/-- **Stacks 07JY.** The category of `Localization S`-modules is equivalent to the full
subcategory of `R`-modules on which every `s ∈ S` acts invertibly. The functor is
`ModuleCat.localizedModuleFunctor` restricted to the subcategory; the quasi-inverse is
restriction of scalars along `algebraMap R (Localization S)`. -/
@[stacks 07JY]
noncomputable def invertibleSMulEquivalentLocalizationModuleCat [Small.{v, u} R] :
    (invertibleSMul S).FullSubcategory ≌ ModuleCat.{v} (Localization S) :=
  CategoryTheory.Equivalence.mk
    (localizedModuleFunctorInvertibleSMul S) (restrictScalarsInvertibleSMul S)
    ((NatIso.ofComponents (localizedModuleFunctorCompResIso S)
      (localizedModuleFunctorCompResIso_naturality S)).symm)
    (NatIso.ofComponents (resCompLocalizedModuleFunctorIso S)
      (resCompLocalizedModuleFunctorIso_hom_naturality S))

instance [Small.{v, u} R] : (localizedModuleFunctorInvertibleSMul S).IsEquivalence :=
  (invertibleSMulEquivalentLocalizationModuleCat S).isEquivalence_functor

end ModuleCat
