module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StalkAdicHomologyBridge
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The stalk of the ideal-power test module, and its pullback

`AlgebraicGeometry.pointTestModule x t` is the `𝒪_X`-module `𝒪_X/𝔪_x^t`, built as the direct
image of the structure sheaf of the closed subscheme cut out by the `t`-th power of the
vanishing ideal sheaf of `closure {x}`. This file computes its stalk and the stalk of its
pullback, and packages the result as the system of ideal-power quotients that the adic
machinery of [Stacks, Tag 0EGV] consumes.

The stalk at a point of the closed subscheme cut out by an ideal sheaf `ℐ` is the quotient of
the local ring of the ambient scheme by the stalk of `ℐ`, so the stalk of `𝒪_X/ℐ^t` is
`𝒪_{X,x}/(ℐ_x)^t`; at a closed point and for the vanishing ideal sheaf of that point the stalk
of the ideal sheaf is the maximal ideal, giving `𝒪_{X,x}/𝔪_x^t`. Along a morphism `g : W ⟶ X`
the stalk of a pullback is the base change of the stalk, and base change carries `R/𝔪^t` to
`S/(𝔪 S)^t`, so the stalk at `z` of `g^*(𝒪_X/𝔪_{g z}^t)` is `𝒪_{W,z}/(𝔪_{g z} · 𝒪_{W,z})^t`.
That ideal is proper, the map on local rings being local.

## Main definitions

* `AlgebraicGeometry.IdealSheafData.subschemePoint`: the point of the closed subscheme cut out
  by an ideal sheaf over a point of the support.
* `AlgebraicGeometry.IdealSheafData.subschemeStalkQuotEquiv` and
  `subschemeStalkQuotLinearEquiv`: `𝒪_{X,x}/ℐ_x ≅ 𝒪_{Z,z}` for `Z` that subscheme.
* `AlgebraicGeometry.IdealSheafData.stalkPushforwardSubschemeQuotEquiv`: the stalk of
  `ι_* 𝒪_Z` is `𝒪_{X,x}/ℐ_x`.
* `AlgebraicGeometry.quotMapPowEquivTensorQuotPow`: the base change `S ⊗_A A/I^t ≅ S/(I S)^t`.
* `AlgebraicGeometry.stalkMapMaximalIdeal`: the ideal `𝔪_{g z} · 𝒪_{W,z}`.
* `AlgebraicGeometry.pullbackPointTestModuleSystem`: the family of single complexes of the
  pulled-back test modules.

## Main results

* `AlgebraicGeometry.IdealSheafData.ker_stalkMap_subschemeι`: the kernel of the map on local
  rings induced by `ℐ.subschemeι` is `ℐ_x`.
* `AlgebraicGeometry.idealPowQuotientStalkEquivOfMemSupport`: the stalk of `𝒪_X/ℐ^t` at a point
  of the support of `ℐ` is `𝒪_{X,x}/(ℐ_x)^t`.
* `AlgebraicGeometry.pointTestModuleStalkEquiv`: the stalk of `𝒪_X/𝔪_x^t` at a closed point `x`
  is `𝒪_{X,x}/𝔪_x^t`.
* `AlgebraicGeometry.pullbackPointTestModuleStalkEquiv`: the stalk at `z` of
  `g^*(𝒪_X/𝔪_{g z}^t)` is `𝒪_{W,z}/(𝔪_{g z} · 𝒪_{W,z})^t`.
* `AlgebraicGeometry.stalkMapMaximalIdeal_ne_top`: that ideal is proper.
* `AlgebraicGeometry.pullbackPointTestModuleSystemIso`: the derived stalks of the pulled-back
  test modules, indexed so that `t` carries the `(t+1)`-st power, are the terms of
  `NoetherianAdicCompletion.idealPowerQuotientSystem`.
* `AlgebraicGeometry.isZero_homology_derivedStalk_of_isZero_homology_pullbackPointTestModule`:
  the adic vanishing criterion at the stalk, run with those test modules.
* `AlgebraicGeometry.finite_modulesStalk_of_isFiniteType` and its corollaries for coherent
  modules and for the cohomology sheaves of a pseudo-coherent or perfect object: finiteness of
  the stalk in the `Stacks.ModuleSkyscraper.modulesStalkFunctor` spelling.

## Implementation notes

No comparison between the `CommRingCat`-valued and the `RingCat`-valued stalk of the structure
sheaf is used. Mathlib's `PresheafOfModules` carries a `Module (R.stalk x)` instance on the
stalk of a presheaf of modules over `R ⋙ forget₂ CommRingCat RingCat`, with `R.stalk` the
`CommRingCat` colimit, and `Stacks.ModuleSkyscraper.modulesStalkFunctor` is valued in modules
over that ring; the whole chain stays on that side. The comparison itself is
`Stacks.PullbackTensorIso.stalkRingIso`, and it is not needed here.

The index convention of `NoetherianAdicCompletion.idealPowerQuotientSystem I` is that its value
at `Opposite.op t` is `A/I^(t+1)`, so `pullbackPointTestModuleSystem` is built from
`pointTestModule _ (t + 1)`; no reindexing isomorphism appears.

`AlgebraicGeometry.IdealSheafData.subschemePoint` is the subtype element `⟨x, hx⟩`: the carrier
of `ℐ.subscheme` is the support of `ℐ` and `Scheme.IdealSheafData.subschemeι_apply` is `rfl`, so
`ℐ.subschemeι (subschemePoint ℐ x hx) = x` holds by `rfl`. That is what lets a statement about
the stalk at `ℐ.subschemeι z` be read as a statement about the stalk at `x` with no transport.

`pullbackPointTestModuleStalkEquiv` installs `Algebra 𝒪_{X,g z} 𝒪_{W,z}` from the map on local
rings by `RingHom.toAlgebra`. `ModuleCat.extendScalars` instead builds its tensor product with
the `Module` instance coming from `ModuleCat.restrictScalars`; the two agree definitionally but
not syntactically, so the three factors of the composite are introduced with their types
ascribed, which is where the definitional check happens.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- For the closed subscheme cut out by an ideal sheaf, the kernel of the induced map of local
rings is the stalk of the ideal sheaf. -/
theorem IdealSheafData.ker_stalkMap_subschemeι (J : X.IdealSheafData) (z : J.subscheme) :
    RingHom.ker (J.subschemeι.stalkMap z).hom = IdealSheafData.stalk J (J.subschemeι z) :=
  (IdealSheafData.stalk_ker_of_isClosedImmersion J.subschemeι z).symm.trans
    (congrArg (fun K : X.IdealSheafData => IdealSheafData.stalk K (J.subschemeι z))
      (Scheme.IdealSheafData.ker_subschemeι J))

/-- The point of the closed subscheme cut out by an ideal sheaf lying over a point of the
support of that ideal sheaf. -/
def IdealSheafData.subschemePoint (J : X.IdealSheafData) (x : X) (hx : x ∈ J.support) :
    J.subscheme := ⟨x, hx⟩

/-- The closed immersion of the subscheme cut out by an ideal sheaf sends
`IdealSheafData.subschemePoint J x hx` to `x`. -/
@[simp]
theorem IdealSheafData.subschemeι_subschemePoint (J : X.IdealSheafData) (x : X)
    (hx : x ∈ J.support) :
    J.subschemeι (IdealSheafData.subschemePoint J x hx) = x := rfl

/-- The local ring of the closed subscheme cut out by an ideal sheaf is the quotient of the
local ring of the ambient scheme by the stalk of the ideal sheaf. -/
def IdealSheafData.subschemeStalkQuotEquiv (J : X.IdealSheafData) (z : J.subscheme) :
    (X.presheaf.stalk (J.subschemeι z) ⧸ IdealSheafData.stalk J (J.subschemeι z)) ≃+*
      J.subscheme.presheaf.stalk z :=
  (Ideal.quotEquivOfEq (IdealSheafData.ker_stalkMap_subschemeι J z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (J.subschemeι.stalkMap_surjective z))

/-- `IdealSheafData.subschemeStalkQuotEquiv` sends the class of `a` to the image of `a` under the
map of stalks induced by the closed immersion. -/
@[simp]
theorem IdealSheafData.subschemeStalkQuotEquiv_mk (J : X.IdealSheafData) (z : J.subscheme)
    (a : X.presheaf.stalk (J.subschemeι z)) :
    IdealSheafData.subschemeStalkQuotEquiv J z
        (Ideal.Quotient.mk (IdealSheafData.stalk J (J.subschemeι z)) a) =
      J.subschemeι.stalkMap z a := by
  simp [IdealSheafData.subschemeStalkQuotEquiv]

/-- `IdealSheafData.subschemeStalkQuotEquiv` as an isomorphism of `𝒪_{X,x}`-modules, where the
local ring of the subscheme is a module over the local ring of the ambient scheme through the map
on stalks. -/
def IdealSheafData.subschemeStalkQuotLinearEquiv (J : X.IdealSheafData) (z : J.subscheme) :
    letI : Module (X.presheaf.stalk (J.subschemeι z)) (J.subscheme.presheaf.stalk z) :=
      Module.compHom (J.subscheme.presheaf.stalk z) (J.subschemeι.stalkMap z).hom
    (X.presheaf.stalk (J.subschemeι z) ⧸ IdealSheafData.stalk J (J.subschemeι z))
      ≃ₗ[X.presheaf.stalk (J.subschemeι z)] J.subscheme.presheaf.stalk z :=
  letI : Module (X.presheaf.stalk (J.subschemeι z)) (J.subscheme.presheaf.stalk z) :=
    Module.compHom (J.subscheme.presheaf.stalk z) (J.subschemeι.stalkMap z).hom
  { toFun := IdealSheafData.subschemeStalkQuotEquiv J z
    map_add' := fun a b => map_add (IdealSheafData.subschemeStalkQuotEquiv J z) a b
    map_smul' := fun r q => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      change IdealSheafData.subschemeStalkQuotEquiv J z
        (Ideal.Quotient.mk (IdealSheafData.stalk J (J.subschemeι z)) (r * a)) = _
      rw [IdealSheafData.subschemeStalkQuotEquiv_mk,
        IdealSheafData.subschemeStalkQuotEquiv_mk]
      exact map_mul (J.subschemeι.stalkMap z).hom r a
    invFun := (IdealSheafData.subschemeStalkQuotEquiv J z).symm
    left_inv := (IdealSheafData.subschemeStalkQuotEquiv J z).left_inv
    right_inv := (IdealSheafData.subschemeStalkQuotEquiv J z).right_inv }

/-- **The stalk of `i_* 𝒪_Z` for `Z` the closed subscheme cut out by an ideal sheaf `J`**: at a
point of `Z` it is `𝒪_{X,x}/J_x`, as a module over `𝒪_{X,x}`. -/
def IdealSheafData.stalkPushforwardSubschemeQuotEquiv (J : X.IdealSheafData)
    (z : J.subscheme) :
    ((Scheme.Modules.pushforward J.subschemeι).obj
        (Stacks.Ample.unitModule J.subscheme)).presheaf.stalk (J.subschemeι z)
      ≃ₗ[X.presheaf.stalk (J.subschemeι z)]
      (X.presheaf.stalk (J.subschemeι z) ⧸ IdealSheafData.stalk J (J.subschemeι z)) :=
  letI : Module (X.presheaf.stalk (J.subschemeι z)) (J.subscheme.presheaf.stalk z) :=
    Module.compHom (J.subscheme.presheaf.stalk z) (J.subschemeι.stalkMap z).hom
  (Stacks.Chow.stalkPushforwardStructureSheafLinearEquiv J.subschemeι z
      (IsClosedImmersion.isClosedEmbedding J.subschemeι).isInducing).trans
    (IdealSheafData.subschemeStalkQuotLinearEquiv J z).symm

/-! ### The stalk of `𝒪_X/ℐ^t` -/

/-- **The stalk of `𝒪_X/ℐ^t`** at a point of the closed subscheme cut out by `ℐ^t`: it is the
quotient of the local ring by the `t`-th power of the stalk of `ℐ`. -/
def idealPowQuotientStalkEquiv (I : X.IdealSheafData) (t : ℕ) (z : (I ^ t).subscheme) :
    (idealPowQuotient I t).presheaf.stalk ((I ^ t).subschemeι z)
      ≃ₗ[X.presheaf.stalk ((I ^ t).subschemeι z)]
      (X.presheaf.stalk ((I ^ t).subschemeι z) ⧸
        IdealSheafData.stalk I ((I ^ t).subschemeι z) ^ t) :=
  (IdealSheafData.stalkPushforwardSubschemeQuotEquiv (I ^ t) z).trans
    (Submodule.quotEquivOfEq _ _ (IdealSheafData.stalk_pow I t ((I ^ t).subschemeι z)))

/-- The point of the closed subscheme cut out by `ℐ^t`, `t ≥ 1`, over a point of the support of
`ℐ`: powers of an ideal sheaf have the same support as the ideal sheaf. -/
def idealPowSubschemePoint (I : X.IdealSheafData) {t : ℕ} (ht : t ≠ 0) (x : X)
    (hx : x ∈ I.support) : (I ^ t).subscheme :=
  IdealSheafData.subschemePoint (I ^ t) x
    (by rwa [Scheme.IdealSheafData.support_pow I t ht])

/-- The closed immersion of the subscheme cut out by `ℐ^t` sends `idealPowSubschemePoint I ht x hx`
to `x`. -/
@[simp]
theorem subschemeι_idealPowSubschemePoint (I : X.IdealSheafData) {t : ℕ} (ht : t ≠ 0) (x : X)
    (hx : x ∈ I.support) :
    (I ^ t).subschemeι (idealPowSubschemePoint I ht x hx) = x := rfl

/-- **The stalk of `𝒪_X/ℐ^t` at a point of the support of `ℐ`** is `𝒪_{X,x}/(ℐ_x)^t`, for
`t ≥ 1`. -/
def idealPowQuotientStalkEquivOfMemSupport (I : X.IdealSheafData) {t : ℕ} (ht : t ≠ 0) (x : X)
    (hx : x ∈ I.support) :
    (idealPowQuotient I t).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x ^ t) :=
  idealPowQuotientStalkEquiv I t (idealPowSubschemePoint I ht x hx)

/-! ### The stalk of the test module at a closed point -/

/-- The stalk at a closed point `x` of the vanishing ideal sheaf of `closure {x}` is the maximal
ideal of `𝒪_{X,x}`. -/
theorem IdealSheafData.stalk_vanishingIdeal_closure_singleton (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IdealSheafData.stalk
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))) x =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have h : Closeds.closure ({x} : Set X) = ⟨{x}, hx⟩ := SetLike.coe_injective hx.closure_eq
  rw [h]
  exact IdealSheafData.stalk_vanishingIdeal_singleton x hx

/-- A point lies in the support of the vanishing ideal sheaf of the closure of that point. -/
theorem mem_support_vanishingIdeal_closure_singleton (x : X) :
    x ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).support :=
  subset_closure rfl

/-- **The stalk of the test module `𝒪_X/𝔪_x^t` at `x` is `𝒪_{X,x}/𝔪_x^t`**, for a closed point
`x` and `t ≥ 1`: the stalk of the direct image of the structure sheaf of a closed subscheme is
the local ring of that subscheme, which is the quotient of `𝒪_{X,x}` by the stalk of the ideal
sheaf, and the stalk of the `t`-th power of the vanishing ideal sheaf of `{x}` is `𝔪_x^t`. -/
def pointTestModuleStalkEquiv (x : X) (hx : IsClosed ({x} : Set X)) {t : ℕ} (ht : t ≠ 0) :
    (pointTestModule x t).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ t) :=
  (idealPowQuotientStalkEquivOfMemSupport
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))) ht x
      (mem_support_vanishingIdeal_closure_singleton x)).trans
    (Submodule.quotEquivOfEq _ _
      (congrArg (· ^ t) (IdealSheafData.stalk_vanishingIdeal_closure_singleton x hx)))

/-! ### The base change of an ideal-power quotient -/

/-- **The base change of `A/I^t`.** For an `A`-algebra `B`, the quotient of `B` by the `t`-th
power of the ideal generated by `I` is `B ⊗_A A/I^t`. -/
def quotMapPowEquivTensorQuotPow {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (t : ℕ) :
    (B ⧸ (I.map (algebraMap A B)) ^ t) ≃ₐ[B] B ⊗[A] (A ⧸ I ^ t) :=
  (Ideal.quotientEquivAlgOfEq B (Ideal.map_pow (algebraMap A B) I t).symm).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (I ^ t))

/-! ### The ideal cut out in a local ring over a point -/

/-- The ideal of `𝒪_{W,z}` generated by the maximal ideal of `𝒪_{X,g z}`: the ideal `𝔪_{g z} ·
𝒪_{W,z}` that an adic argument along `g` runs with. -/
def stalkMapMaximalIdeal {W : Scheme.{u}} (g : W ⟶ X) (z : W) : Ideal (W.presheaf.stalk z) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk (g.base z))).map (g.stalkMap z).hom

/-- **`𝔪_{g z} · 𝒪_{W,z}` is a proper ideal**: the map on stalks is a local homomorphism, so the
image of the maximal ideal lands in the maximal ideal. -/
theorem stalkMapMaximalIdeal_ne_top {W : Scheme.{u}} (g : W ⟶ X) (z : W) :
    stalkMapMaximalIdeal g z ≠ ⊤ :=
  (IsLocalRing.map_maximalIdeal_lt_top (g.stalkMap z).hom).ne

/-- The `t`-th power of `𝔪_{g z} · 𝒪_{W,z}` is the ideal generated by `𝔪_{g z}^t`. -/
theorem stalkMapMaximalIdeal_pow {W : Scheme.{u}} (g : W ⟶ X) (z : W) (t : ℕ) :
    stalkMapMaximalIdeal g z ^ t =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (g.base z)) ^ t).map (g.stalkMap z).hom :=
  (Ideal.map_pow (g.stalkMap z).hom _ t).symm

/-- **The stalk of the pullback of the test module.** For `g : W ⟶ X`, a point `z` of `W` over
a closed point `g z` of `X`, and `t ≥ 1`, the stalk at `z` of `g^*(𝒪_X/𝔪_{g z}^t)` is
`𝒪_{W,z}/(𝔪_{g z} · 𝒪_{W,z})^t`: the stalk of a pullback is the base change of the stalk, and
base change carries `R/𝔪^t` to `S/(𝔪 S)^t`. -/
def pullbackPointTestModuleStalkEquiv {W : Scheme.{u}} (g : W ⟶ X) (z : W)
    (hx : IsClosed ({g z} : Set X)) {t : ℕ} (ht : t ≠ 0) :
    ((Scheme.Modules.pullback g).obj (pointTestModule (g z) t)).presheaf.stalk z
      ≃ₗ[W.presheaf.stalk z] (W.presheaf.stalk z ⧸ stalkMapMaximalIdeal g z ^ t) :=
  letI : Algebra (X.presheaf.stalk (g z)) (W.presheaf.stalk z) :=
    (g.stalkMap z).hom.toAlgebra
  let eStalk : ((Scheme.Modules.pullback g).obj (pointTestModule (g z) t)).presheaf.stalk z
      ≃ₗ[W.presheaf.stalk z]
      (W.presheaf.stalk z) ⊗[X.presheaf.stalk (g z)]
        ((pointTestModule (g z) t).presheaf.stalk (g z)) :=
    (Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv g z (pointTestModule (g z) t)).symm
  let eBase : (W.presheaf.stalk z) ⊗[X.presheaf.stalk (g z)]
        ((pointTestModule (g z) t).presheaf.stalk (g z))
      ≃ₗ[W.presheaf.stalk z] (W.presheaf.stalk z) ⊗[X.presheaf.stalk (g z)]
        (X.presheaf.stalk (g z) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk (g z)) ^ t) :=
    LinearEquiv.baseChange (X.presheaf.stalk (g z)) (W.presheaf.stalk z) _ _
      (pointTestModuleStalkEquiv (g z) hx ht)
  let eQuot : (W.presheaf.stalk z) ⊗[X.presheaf.stalk (g z)]
        (X.presheaf.stalk (g z) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk (g z)) ^ t)
      ≃ₗ[W.presheaf.stalk z] (W.presheaf.stalk z ⧸ stalkMapMaximalIdeal g z ^ t) :=
    (quotMapPowEquivTensorQuotPow (W.presheaf.stalk z)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (g z))) t).symm.toLinearEquiv
  eStalk.trans (eBase.trans eQuot)

/-! ### Finiteness of the stalk, in the `modulesStalkFunctor` spelling -/

/-- **The stalk of a module of finite type is a finite module over the local ring.** Stated for
the stalk functor `Stacks.ModuleSkyscraper.modulesStalkFunctor`, which is the spelling a
statement about `D(𝒪_{X,x})` is phrased in. -/
theorem finite_modulesStalk_of_isFiniteType (F : X.Modules) [F.IsFiniteType] (x : X) :
    Module.Finite (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
  SheafOfModules.finite_stalk X.sheaf F x

/-- The stalk of a coherent module on a locally Noetherian scheme is finite over the local
ring, in the `modulesStalkFunctor` spelling. -/
theorem finite_modulesStalk_of_isCoherent (F : X.Modules) (hF : F.IsCoherent) (x : X) :
    Module.Finite (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj F) :=
  have : F.IsFiniteType := hF.isFiniteType
  finite_modulesStalk_of_isFiniteType F x

section DerivedStalk

attribute [local instance] HasDerivedCategory.standard

/-- **The stalks of the cohomology sheaves of a pseudo-coherent object are finite modules over
the local ring**, in every degree and in the `modulesStalkFunctor` spelling: on a locally
Noetherian scheme those sheaves are coherent. -/
theorem finite_modulesStalk_homology_of_isPseudoCoherent (X : Scheme.{u})
    [IsLocallyNoetherian X] (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (x : X) (i : ℤ) :
    Module.Finite (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) :=
  finite_modulesStalk_of_isCoherent _ (isCoherent_homology_of_isPseudoCoherent X E hE i) x

/-- **The stalks of the cohomology sheaves of a perfect object are finite modules over the local
ring**, in every degree and in the `modulesStalkFunctor` spelling. -/
theorem finite_modulesStalk_homology_of_isPerfect (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (x : X) (i : ℤ) :
    Module.Finite (X.presheaf.stalk x)
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) :=
  finite_modulesStalk_homology_of_isPseudoCoherent X E hE.isPseudoCoherent x i

/-! ### The ideal-power quotient system of stalks -/

/-- **The system of stalks fed to the adic machinery.** For `g : W ⟶ X` and a point `z` of `W`
over a closed point `g z`, the derived stalk at `z` of the single complex of
`g^*(𝒪_X/𝔪_{g z}^{t+1})` is the `t`-th term of `NoetherianAdicCompletion`'s system of quotients
by the powers of `𝔪_{g z} · 𝒪_{W,z}`. -/
def pullbackPointTestModuleDerivedStalkIso {W : Scheme.{u}} (g : W ⟶ X) (z : W)
    (hx : IsClosed ({g z} : Set X)) (t : ℕ) :
    (derivedStalkFunctor z).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pullback g).obj (pointTestModule (g z) (t + 1))))
      ≅ (NoetherianAdicCompletion.idealPowerQuotientSystem
          (stalkMapMaximalIdeal g z)).obj (Opposite.op t) :=
  ((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapDerivedCategorySingleFunctor 0).app
      ((Scheme.Modules.pullback g).obj (pointTestModule (g z) (t + 1))) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk z)) 0).mapIso
      (pullbackPointTestModuleStalkEquiv g z hx (Nat.succ_ne_zero t)).toModuleIso ≪≫
    (DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso
      ComplexShape.embeddingDownNat
      (ModuleCat.of (W.presheaf.stalk z)
        (W.presheaf.stalk z ⧸ stalkMapMaximalIdeal g z ^ (t + 1))) 0 0 (by simp))).symm

/-- The family of objects of `D(𝒪_W)` that the adic stalk bridge is fed: the single complexes
of the pulled-back test modules `g^*(𝒪_X/𝔪_{g z}^{t+1})`. -/
def pullbackPointTestModuleSystem {W : Scheme.{u}} (g : W ⟶ X) (z : W) :
    ℕ → DerivedCategory W.Modules := fun t =>
  (DerivedCategory.singleFunctor W.Modules 0).obj
    ((Scheme.Modules.pullback g).obj (pointTestModule (g z) (t + 1)))

/-- **The input `h𝓖` of `isZero_homology_derivedStalk_of_isZero_homology_sheafTensor`**: the
derived stalks of the pulled-back test modules form the ideal-power quotient system of
`𝔪_{g z} · 𝒪_{W,z}`. -/
def pullbackPointTestModuleSystemIso {W : Scheme.{u}} (g : W ⟶ X) (z : W)
    (hx : IsClosed ({g z} : Set X)) (t : ℕ) :
    (derivedStalkFunctor z).obj (pullbackPointTestModuleSystem g z t) ≅
      (NoetherianAdicCompletion.idealPowerQuotientSystem
        (stalkMapMaximalIdeal g z)).obj (Opposite.op t) :=
  pullbackPointTestModuleDerivedStalkIso g z hx t

/-- **[Stacks, Tag 0EGV] run with the pulled-back test modules.** Let `z` be a point of `W` with
Noetherian local ring, lying over a closed point `g z` of `X`, let `T` be a derived tensor
product on `D(𝒪_W)` and `𝒯` one on `D(𝒪_{W,z})` matched by `hstalk`. If `K_z` is pseudo-coherent
and the `i`-th cohomology sheaf of `T(K, g^*(𝒪_X/𝔪_{g z}^{t+1}))` vanishes for every `t`, then
`Hⁱ(K_z) = 0`. The ideal and its properness are discharged here, not assumed. -/
theorem isZero_homology_derivedStalk_of_isZero_homology_pullbackPointTestModule
    {W : Scheme.{u}} (g : W ⟶ X) (z : W) (hx : IsClosed ({g z} : Set X))
    [IsNoetherianRing (W.presheaf.stalk z)]
    (T : DerivedCategory W.Modules ⥤ DerivedCategory W.Modules ⥤ DerivedCategory W.Modules)
    (𝒯 : CochainComplex.DerivedTensor.DerivedTensorProduct (W.presheaf.stalk z))
    (hstalk : ∀ E F : DerivedCategory W.Modules,
      (derivedStalkFunctor z).obj ((T.obj E).obj F) ≅
        (𝒯.tensor.obj ((derivedStalkFunctor z).obj E)).obj ((derivedStalkFunctor z).obj F))
    (K : DerivedCategory W.Modules)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedStalkFunctor z).obj K)) (i : ℤ)
    (hvan : ∀ t : ℕ, IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((T.obj K).obj (pullbackPointTestModuleSystem g z t)))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (W.presheaf.stalk z)) i).obj
      ((derivedStalkFunctor z).obj K)) :=
  isZero_homology_derivedStalk_of_isZero_homology_sheafTensor z T 𝒯 hstalk
    (stalkMapMaximalIdeal g z) (stalkMapMaximalIdeal_ne_top g z)
    (pullbackPointTestModuleSystem g z) (pullbackPointTestModuleSystemIso g z hx) K hK i hvan

end DerivedStalk

end AlgebraicGeometry

end
