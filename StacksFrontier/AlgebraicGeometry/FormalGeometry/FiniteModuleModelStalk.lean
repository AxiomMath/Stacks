module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel

/-!
# The stalks of a finite module model are localizations

Fix an algebraization situation, with `X = Spec(A)` and `U = X \ V(𝔞)`, and let `(M_n)` be an
inverse system of `A`-modules, so that `(M_n^~|_U)` is an inverse system of `𝒪_U`-modules. At
a point `y ∈ U` lying over the prime `𝔭` of `A`, the stalk of `M_n^~|_U` at `y` is the
localization `(M_n)_𝔭`, naturally in `n`: this file constructs the canonical maps
`M_n → (M_n^~|_U)_y` and proves that each is a localization at `A \ 𝔭`, for the `A`-module
structure on the stalk through the canonical ring map `A → 𝒪_{U,y}`.

This is the comparison between the coherent adic system `(ℱ_n)` of a finite module model and
the model itself at the level of stalks, the input needed to read a statement about the formal
stalk `ℱ_y^∧ = lim ℱ_{n,y}` of Stacks 0EJ3 in terms of the modules `M_n`.

## Main definitions

* `Stacks.Algebraization.specStalkRingHom` — the ring map `R → 𝒪_{Spec R, x}` through the germ
  of a global section.
* `Stacks.Algebraization.tildeToStalk` — the natural map `N → (N^~)_x`, `R`-linear for the
  action through `specStalkRingHom`.
* `Stacks.Algebraization.pullbackStalkOpenImmersionIso` — for an open immersion `f : W ⟶ Y`, the
  stalk of `f^* P` at `w`, as a module over the ring of the target through `f^♯_w`, is the stalk
  of `P` at `f w`, naturally in `P`.
* `Stacks.Algebraization.restrictedTildeToStalk` — the natural map
  `N → (N^~|_U)_y` of `A`-modules.
* `Stacks.Algebraization.restrictedTildeSystemToStalk` — the same maps along an inverse system
  `(M_n)`, into the stalks of `Stacks.Algebraization.restrictedTildeSystem`.

## Main results

* `Stacks.Algebraization.isLocalizedModule_tildeToStalk` — `N → (N^~)_x` is a localization at
  the complement of `x`.
* `Stacks.Algebraization.isLocalizedModule_restrictedTildeToStalk` — `N → (N^~|_U)_y` is a
  localization at the complement of the prime under `y`.
* `Stacks.Algebraization.isLocalizedModule_restrictedTildeSystemToStalk` — the same, levelwise
  along `(M_n)`. Together with `Stacks.Algebraization.completedStalkQuotientEquivStalk` this
  identifies the reductions `ℱ_y^∧ / I^{n+1} ℱ_y^∧` of the formal stalk with `(M_n)_𝔭`.

## Implementation notes

The stalk is taken with `Stacks.ModuleSkyscraper.modulesStalkFunctor`, whose value at an
`𝒪_X`-module is the stalk of its underlying presheaf of abelian groups with Mathlib's action of
`𝒪_{X,x}`; this is the spelling in which the stalk of a pullback is computed
(`Stacks.ModuleSkyscraper.pullbackStalkIso`). The `A`-module structure is a restriction of
scalars, so that the maps assemble into natural transformations of functors to `A`-modules.

The stalk map of an open immersion is an isomorphism of rings, so extension of scalars along it
is an equivalence and the unit `P → f^♯_* (𝒪_{W,w} ⊗ P)` is an isomorphism; that is how the tensor
product in the stalk formula of a pullback disappears.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098), the stalk of a
  pullback.
* [Stacks Project, Tag 0DXT](https://stacks.math.columbia.edu/tag/0DXT), the finite module
  model.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the formal stalk.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

/-! ### The stalk of `N^~` -/

section Spec

variable {R : CommRingCat.{u}}

/-- The ring map `R → 𝒪_{Spec R, x}` sending `r` to the germ at `x` of the global section `r`. -/
public def specStalkRingHom (x : PrimeSpectrum.Top R) : R →+* (Spec R).presheaf.stalk x :=
  ((Spec R).presheaf.germ ⊤ x (Set.mem_univ _)).hom.comp (Scheme.ΓSpecIso R).inv.hom

/-- `specStalkRingHom` is the structure map `StructureSheaf.toStalk`. -/
public theorem specStalkRingHom_eq (x : PrimeSpectrum.Top R) :
    specStalkRingHom x = (StructureSheaf.toStalk R x).hom := by
  rw [specStalkRingHom, Scheme.ΓSpecIso_inv]
  rfl

/-- Mathlib's `R`-module structure on the stalk of `N^~` is the restriction of the action of the
local ring along `specStalkRingHom`. -/
public def tildeStalkEquiv (N : ModuleCat.{u} R) (x : PrimeSpectrum.Top R) :
    (tilde N).presheaf.stalk x ≃ₗ[R]
      (ModuleCat.restrictScalars (specStalkRingHom x)).obj
        ((modulesStalkFunctor (Spec R) x).obj (tilde N)) where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' r m := by
    rw [RingHom.id_apply, specStalkRingHom_eq]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The map `N → (N^~)_x`, as an `R`-linear map for the action through `specStalkRingHom`. -/
public def tildeToStalk (N : ModuleCat.{u} R) (x : PrimeSpectrum.Top R) :
    N →ₗ[R] (ModuleCat.restrictScalars (specStalkRingHom x)).obj
        ((modulesStalkFunctor (Spec R) x).obj (tilde N)) :=
  (tildeStalkEquiv N x).toLinearMap ∘ₗ (tilde.toStalk N x).hom

/-- **`N → (N^~)_x` is a localization at the complement of `x`.** -/
public instance isLocalizedModule_tildeToStalk (N : ModuleCat.{u} R) (x : PrimeSpectrum.Top R) :
    IsLocalizedModule x.asIdeal.primeCompl (tildeToStalk N x) :=
  IsLocalizedModule.of_linearEquiv _ _ _

/-- The map `N → (N^~)_x` is natural in `N`. -/
public theorem tildeToStalk_naturality {N N' : ModuleCat.{u} R} (g : N ⟶ N')
    (x : PrimeSpectrum.Top R) (n : N) :
    ((modulesStalkFunctor (Spec R) x).map (tilde.map g)).hom (tildeToStalk N x n) =
      tildeToStalk N' x (g n) := by
  show ((modulesStalkFunctor (Spec R) x).map (tilde.map g)).hom
      (((tilde N).presheaf.germ ⊤ x trivial).hom ((tilde.toOpen N ⊤).hom n)) =
    ((tilde N').presheaf.germ ⊤ x trivial).hom ((tilde.toOpen N' ⊤).hom (g n))
  refine (modulesStalkFunctor_map_germ (X := Spec R) (tilde.map g) x ⊤ trivial _).trans ?_
  congr 1
  exact congr($(tilde.toOpen_map_app g ⊤).hom n)

/-- The maps `N → (N^~)_x`, as a natural transformation of functors to `R`-modules. -/
public def tildeToStalkNatTrans (x : PrimeSpectrum.Top R) :
    𝟭 (ModuleCat.{u} R) ⟶ tilde.functor R ⋙ modulesStalkFunctor (Spec R) x ⋙
      ModuleCat.restrictScalars (specStalkRingHom x) where
  app N := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (specStalkRingHom x)).obj
    ((modulesStalkFunctor (Spec R) x).obj (tilde N))) (tildeToStalk N x)
  naturality _ _ g := by
    ext n
    exact (tildeToStalk_naturality g x n).symm

end Spec

/-! ### The stalk of a pullback along an open immersion -/

section OpenImmersion

variable {W Y : Scheme.{u}} (f : W ⟶ Y) [IsOpenImmersion f] (w : W)

/-- The stalk map of an open immersion, as an equivalence of rings. -/
public def stalkMapRingEquiv : Y.presheaf.stalk (f.base w) ≃+* W.presheaf.stalk w :=
  RingEquiv.ofBijective (f.stalkMap w).hom (ConcreteCategory.bijective_of_isIso _)

/-- Extension of scalars along the stalk map of an open immersion is an equivalence, so the unit
of the extension-restriction adjunction is an isomorphism. -/
public instance isIso_extendRestrictScalarsAdj_unit_stalkMap :
    IsIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (f.stalkMap w).hom).unit := by
  have : (ModuleCat.restrictScalars.{u} (stalkMapRingEquiv f w).toRingHom).IsEquivalence :=
    inferInstance
  have : (ModuleCat.restrictScalars.{u} (f.stalkMap w).hom).IsEquivalence := this
  have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (f.stalkMap w).hom).isEquivalence_left_of_isEquivalence_right
  infer_instance

/-- **The stalk of a pullback along an open immersion.** The stalk of `f^* P` at `w`, as a module
over `𝒪_{Y, f w}` through the stalk map, is the stalk of `P` at `f w`, naturally in `P`. -/
public def pullbackStalkOpenImmersionIso :
    Scheme.Modules.pullback f ⋙ modulesStalkFunctor W w ⋙
        ModuleCat.restrictScalars.{u} (f.stalkMap w).hom ≅
      modulesStalkFunctor Y (f.base w) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackStalkIso f w).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (modulesStalkFunctor Y (f.base w))
      (asIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (f.stalkMap w).hom).unit).symm ≪≫
    Functor.rightUnitor _

/-- The same comparison after a further restriction of scalars along a ring map `ρ` into
`𝒪_{Y, f w}`. -/
public def pullbackStalkOpenImmersionRestrictIso {T : Type u} [CommRing T]
    (ρ : T →+* Y.presheaf.stalk (f.base w)) :
    Scheme.Modules.pullback f ⋙ modulesStalkFunctor W w ⋙
        ModuleCat.restrictScalars.{u} ((f.stalkMap w).hom.comp ρ) ≅
      modulesStalkFunctor Y (f.base w) ⋙ ModuleCat.restrictScalars.{u} ρ :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Functor.isoWhiskerLeft (modulesStalkFunctor W w)
        (ModuleCat.restrictScalarsComp'.{u} ρ (f.stalkMap w).hom _ rfl)) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackStalkOpenImmersionIso f w) _

end OpenImmersion

/-! ### The stalks of `N^~|_U` -/

section Situation

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme)

/-- The canonical ring map `A → 𝒪_{U,y}` is the stalk map of `U → X` after the germ of a global
section. -/
public theorem baseToPointStalk_eq :
    baseToPointStalk S y =
      (S.U.ι.stalkMap y).hom.comp (specStalkRingHom (R := .of S.A) (S.U.ι.base y)) :=
  rfl

/-- **The natural map `N → (N^~|_U)_y`**, of `A`-modules, the stalk carrying its `A`-module
structure through `Stacks.Algebraization.baseToPointStalk`. -/
public def restrictedTildeToStalk :
    𝟭 (ModuleCat.{u} S.A) ⟶ tilde.functor (.of S.A) ⋙ Scheme.Modules.pullback S.U.ι ⋙
      modulesStalkFunctor S.U.toScheme y ⋙ ModuleCat.restrictScalars.{u} (baseToPointStalk S y) :=
  tildeToStalkNatTrans (R := .of S.A) (S.U.ι.base y) ≫
    Functor.whiskerLeft (tilde.functor (.of S.A))
      (pullbackStalkOpenImmersionRestrictIso S.U.ι y
        (specStalkRingHom (R := .of S.A) (S.U.ι.base y))).inv

/-- **`N → (N^~|_U)_y` is a localization at the complement of the prime under `y`.** -/
public instance isLocalizedModule_restrictedTildeToStalk (N : ModuleCat.{u} S.A) :
    IsLocalizedModule (underlyingPrime S y).asIdeal.primeCompl
      ((restrictedTildeToStalk S y).app N).hom := by
  have : IsLocalizedModule (underlyingPrime S y).asIdeal.primeCompl
      ((tildeToStalkNatTrans (R := .of S.A) (S.U.ι.base y)).app N).hom :=
    isLocalizedModule_tildeToStalk (R := .of S.A) N (S.U.ι.base y)
  exact IsLocalizedModule.of_linearEquiv _ _
    (((pullbackStalkOpenImmersionRestrictIso S.U.ι y
      (specStalkRingHom (R := .of S.A) (S.U.ι.base y))).app
        ((tilde.functor (.of S.A)).obj N)).symm.toLinearEquiv)

/-- **The stalks of the system `(M_n^~|_U)` at `y`.** The natural maps `M_n → (M_n^~|_U)_y` of
`Stacks.Algebraization.restrictedTildeToStalk`, as a morphism of inverse systems of `A`-modules
out of `(M_n)`. For a finite module model `M`, the target is the system of stalks at `y` of the
coherent adic system `Stacks.Algebraization.coherentAdicSystemOfFiniteModuleModel`, whose limit
is the formal stalk `ℱ_y^∧`. -/
public def restrictedTildeSystemToStalk (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A) :
    M ⟶ restrictedTildeSystem S M ⋙ modulesStalkFunctor S.U.toScheme y ⋙
      ModuleCat.restrictScalars.{u} (baseToPointStalk S y) :=
  Functor.whiskerLeft M (restrictedTildeToStalk S y)

/-- Each component of `Stacks.Algebraization.restrictedTildeSystemToStalk` is a localization at
the complement of the prime under `y`: the stalk of `M_n^~|_U` at `y` is `(M_n)_𝔭`. -/
public instance isLocalizedModule_restrictedTildeSystemToStalk (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)
    (n : ℕᵒᵖ) :
    IsLocalizedModule (underlyingPrime S y).asIdeal.primeCompl
      ((restrictedTildeSystemToStalk S y M).app n).hom :=
  isLocalizedModule_restrictedTildeToStalk S y (M.obj n)

end Situation

end Stacks.Algebraization

end
