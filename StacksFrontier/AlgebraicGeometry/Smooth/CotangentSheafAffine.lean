module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafScheme

/-!
# The affine comparison map for the sheaf of relative differentials

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an open of `S` and `W` an open of `X` with
`W ≤ f ⁻¹ᵁ V`, and let `a : T ⟶ X` be a morphism with `U ≤ a ⁻¹ᵁ W` for an open `U` of `T`. Write
`R = Γ(S, V)`, `B = Γ(X, W)` and `A = Γ(T, U)`. Stacks Project, Tag 01UM computes the sections of
`Ω_{X/S}` over an affine open in terms of Kähler differentials; this file constructs the
comparison map that such a computation asserts to be an isomorphism, in the pullback form
`A ⊗[B] Ω[B⁄R] ⟶ Γ(a^*Ω_{X/S}, U)`, together with its characterizing property, its uniqueness,
and its naturality in `U`.

## Main definitions

* `Stacks.Smooth.algebraAppLE`, `Stacks.Smooth.moduleAppLE` and
  `Stacks.Smooth.moduleAppLEBase` are the algebra and module structures on section rings and
  section modules obtained by restricting scalars along `AlgebraicGeometry.Scheme.Hom.appLE`.
* `Stacks.Smooth.universalD` is the universal differential `Γ(X, W) ⟶ Γ(Ω_{X/S}, W)` and
  `Stacks.Smooth.pullbackD` is its pullback along `a`, restricted to `U`.
* `Stacks.Smooth.pullbackCotangentDerivation` packages `pullbackD` as an `R`-derivation of `B`
  with values in `Γ(a^*Ω_{X/S}, U)`.
* `Stacks.Smooth.cotangentComparison` is the induced `A`-linear map
  `A ⊗[B] Ω[B⁄R] ⟶ Γ(a^*Ω_{X/S}, U)`.

## Main results

* `Stacks.Smooth.universalD_appLE` says that the universal differential of `Ω_{X/S}` kills the
  image of `Γ(S, V)` in `Γ(X, W)`. This is the one place where the structure map
  `f⁻¹𝒪_S ⟶ 𝒪_X` enters, and it is what makes `pullbackCotangentDerivation` a derivation over
  `R` rather than merely over the sections of `f⁻¹𝒪_S`.
* `Stacks.Smooth.cotangentComparison_one_tmul_D` is the characterizing property: the comparison
  map carries `1 ⊗ d b` to the pullback of the universal differential of `b`, and
  `Stacks.Smooth.cotangentComparison_unique` says that this property determines it.
* `Stacks.Smooth.map_cotangentComparison` is the naturality: for `U' ≤ U` the comparison maps
  commute with restriction of sections on the one side and with base change along
  `Γ(T, U) ⟶ Γ(T, U')` on the other. Specialized to `U = ⊤` and `U' = T.basicOpen g` this is
  naturality with respect to restriction to the basic opens of an affine `T`.
* `Stacks.Smooth.isLocalizedModule_rTensor_basicOpen` records that the base-change side of that
  square is a localization away from `g`, which is what the Čech step of Stacks Project,
  Tag 02H6 consumes.

## Implementation notes

The comparison map is built from the universal property of `Ω_{X/S}` and not by computing
sections. The unit of the adjunction `a^* ⊣ a_*` of `AlgebraicGeometry.Scheme.Modules` gives a
map on sections `Γ(Ω_{X/S}, W) ⟶ Γ(a^*Ω_{X/S}, a ⁻¹ᵁ W)` which is semilinear over
`a^♯ : Γ(X, W) ⟶ Γ(T, a ⁻¹ᵁ W)`; composing the universal derivation with it and restricting to
`U` gives a derivation of `B` with values in `Γ(a^*Ω_{X/S}, U)`, and
`Derivation.liftKaehlerDifferential` followed by `LinearMap.liftBaseChange` turns that into the
displayed `A`-linear map.

For `W ≤ f ⁻¹ᵁ V` the ring `Γ(X, W)` is not an algebra over `Γ(S, V)` by instance search, since
the relation `W ≤ f ⁻¹ᵁ V` is not recoverable from the types; as in
`StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange` the relevant `Algebra`, `Module`
and `IsScalarTower` instances are therefore provided explicitly and appear as `letI`s in the
statements below.

What this file does *not* provide, but what is proved in
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentBijective`, is bijectivity of
`Stacks.Smooth.cotangentComparison` — the actual content of the affine computation of Tag 01UM.
Bijectivity is a statement about the sheafification that produces `Ω_{X/S}`: an inverse has to
spread a ring derivation of `B` out into a derivation of `𝒪_X` with values in `a_*N`, which
means extending it over the basic opens of `W` — where it extends uniquely, because a derivation
extends uniquely along a localization — and then gluing. None of the hypotheses that bijectivity
needs (affineness of `V`, `W` and `T`) is needed for the comparison map itself, so they are not
assumed here.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 01UR](https://stacks.math.columbia.edu/tag/01UR)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Stacks.Sheaves.RingedSpaceDifferentials

universe u

namespace Stacks.Smooth

/-! ### Algebra and module structures along `appLE` -/

/-- The `Γ(S, V)`-algebra structure on `Γ(X, W)` induced by `f : X ⟶ S` for `W ≤ f ⁻¹ᵁ V`. -/
@[instance_reducible]
noncomputable def algebraAppLE {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {W : X.Opens}
    (hWV : W ≤ f ⁻¹ᵁ V) : Algebra Γ(S, V) Γ(X, W) :=
  (f.appLE V W hWV).hom.toAlgebra

/-- The `Γ(X, W)`-module structure on `Γ(M, U)`, for `M` a module on `T`, `a : T ⟶ X` and
`U ≤ a ⁻¹ᵁ W`, obtained by restricting scalars along `a.appLE W U`. -/
@[instance_reducible]
noncomputable def moduleAppLE {X T : Scheme.{u}} (a : T ⟶ X) (M : T.Modules) {W : X.Opens}
    {U : T.Opens} (hUW : U ≤ a ⁻¹ᵁ W) : Module Γ(X, W) Γ(M, U) :=
  Module.compHom _ (a.appLE W U hUW).hom

/-- The scalar tower `Γ(X, W) → Γ(T, U) → Γ(M, U)`. -/
theorem isScalarTowerAppLE {X T : Scheme.{u}} (a : T ⟶ X) (M : T.Modules) {W : X.Opens}
    {U : T.Opens} (hUW : U ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE a hUW
    letI := moduleAppLE a M hUW
    IsScalarTower Γ(X, W) Γ(T, U) Γ(M, U) :=
  let := algebraAppLE a hUW
  let := moduleAppLE a M hUW
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The `Γ(S, V)`-module structure on `Γ(M, U)` obtained by restricting scalars along the
composite `Γ(S, V) ⟶ Γ(X, W) ⟶ Γ(T, U)`. -/
@[instance_reducible]
noncomputable def moduleAppLEBase {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (M : T.Modules)
    {V : S.Opens} {W : X.Opens} {U : T.Opens} (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) :
    Module Γ(S, V) Γ(M, U) :=
  Module.compHom _ (f.appLE V W hWV ≫ a.appLE W U hUW).hom

/-- The scalar tower `Γ(S, V) → Γ(X, W) → Γ(M, U)`. -/
theorem isScalarTowerAppLEBase {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (M : T.Modules)
    {V : S.Opens} {W : X.Opens} {U : T.Opens} (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := moduleAppLE a M hUW
    letI := moduleAppLEBase f a M hWV hUW
    IsScalarTower Γ(S, V) Γ(X, W) Γ(M, U) :=
  let := algebraAppLE f hWV
  let := moduleAppLE a M hUW
  let := moduleAppLEBase f a M hWV hUW
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-! ### The universal differential on sections -/

section Universal

variable {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens) {V : S.Opens}

/-- The universal differential `d : Γ(X, W) ⟶ Γ(Ω_{X/S}, W)` on sections over an open `W`: the
component at `W` of the universal derivation of `Ω_{X/S}`. -/
noncomputable def universalD : Γ(X, W) →+ Γ(cotangentSheaf f, W) :=
  (universalDerivation (ringedSpaceHom f)).d

/-- The Leibniz rule for the universal differential. -/
theorem universalD_mul (b₁ b₂ : Γ(X, W)) :
    universalD f W (b₁ * b₂) = b₁ • universalD f W b₂ + b₂ • universalD f W b₁ :=
  (universalDerivation (ringedSpaceHom f)).d_mul b₁ b₂

/-- The universal differential of the unit section vanishes. -/
theorem universalD_one : universalD f W 1 = 0 :=
  PresheafOfModulesOfCommRing.Derivation.d_one _ (op W)

/-- The unit of the adjunction `f⁻¹ ⊣ f_*` between sheaves of commutative rings, at the
structure sheaf of `S`. -/
noncomputable abbrev inverseImageUnit : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u}
    (ringedSpaceHom f).hom.base).obj (inverseImageSheaf (ringedSpaceHom f)) :=
  (sheafAdjunction (ringedSpaceHom f)).unit.app S.sheaf

/-- The canonical section of `f⁻¹𝒪_S` over `W` attached to a section `r` of `𝒪_S` over `V`, for
`W ≤ f ⁻¹ᵁ V`: the image of `r` under the unit of `f⁻¹ ⊣ f_*`, restricted to `W`. -/
noncomputable def inverseImageSection (hWV : W ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    (inverseImageSheaf (ringedSpaceHom f)).obj.obj (op W) :=
  ((inverseImageSheaf (ringedSpaceHom f)).obj.map (homOfLE hWV).op).hom
    (((inverseImageUnit f).hom.app (op V)).hom r)

/-- The structure map `f⁻¹𝒪_S ⟶ 𝒪_X` carries `inverseImageSection f W hWV r` to the image of
`r` under `f.appLE V W hWV`. In other words, the image of `Γ(S, V)` in `Γ(X, W)` is contained in
the image of the sections of `f⁻¹𝒪_S` over `W`. -/
theorem inverseImageStructureMap_inverseImageSection (hWV : W ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    ((inverseImageStructureMap (ringedSpaceHom f)).hom.app (op W)).hom
        (inverseImageSection f W hWV r) = (f.appLE V W hWV).hom r := by
  have key : inverseImageUnit f ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (ringedSpaceHom f).hom.base).map (inverseImageStructureMap (ringedSpaceHom f))
      = structureSheafMap (ringedSpaceHom f) :=
    (Adjunction.homEquiv_unit (sheafAdjunction (ringedSpaceHom f)) S.sheaf X.sheaf
      (inverseImageStructureMap (ringedSpaceHom f))).symm.trans
      (homEquiv_inverseImageStructureMap (ringedSpaceHom f))
  have hsq : (inverseImageUnit f).hom.app (op V) ≫
      (inverseImageStructureMap (ringedSpaceHom f)).hom.app (op (f ⁻¹ᵁ V)) = f.app V :=
    congrFun (congrArg NatTrans.app (Sheaf.hom_ext_iff.mp key)) (op V)
  have hnat := (inverseImageStructureMap (ringedSpaceHom f)).hom.naturality (homOfLE hWV).op
  have h1 : ((inverseImageStructureMap (ringedSpaceHom f)).hom.app (op W)).hom
        (inverseImageSection f W hWV r)
      = (X.presheaf.map (homOfLE hWV).op).hom
        (((inverseImageStructureMap (ringedSpaceHom f)).hom.app (op (f ⁻¹ᵁ V))).hom
          (((inverseImageUnit f).hom.app (op V)).hom r)) :=
    congr($(hnat).hom (((inverseImageUnit f).hom.app (op V)).hom r))
  rw [h1, show ((inverseImageStructureMap (ringedSpaceHom f)).hom.app (op (f ⁻¹ᵁ V))).hom
      (((inverseImageUnit f).hom.app (op V)).hom r) = (f.app V).hom r from congr($(hsq).hom r)]
  rfl

/-- **The universal differential kills the base.** The universal differential of the image in
`Γ(X, W)` of a section of `𝒪_S` over an open `V` containing the image of `W` vanishes. -/
theorem universalD_appLE (hWV : W ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) :
    universalD f W ((f.appLE V W hWV).hom r) = 0 := by
  rw [show universalD f W ((f.appLE V W hWV).hom r)
      = (universalDerivation (ringedSpaceHom f)).d ((f.appLE V W hWV).hom r) from rfl,
    ← inverseImageStructureMap_inverseImageSection f W hWV r]
  exact PresheafOfModulesOfCommRing.Derivation'.d_app (universalDerivation (ringedSpaceHom f)) _

end Universal

/-! ### The pullback of the universal derivation -/

section Derivation

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (W : X.Opens) {V : S.Opens}
  {U U' : T.Opens}

/-- The unit `Ω_{X/S} ⟶ a_* a^* Ω_{X/S}` of the adjunction between pullback and pushforward of
sheaves of modules on schemes. -/
noncomputable abbrev pullbackCotangentUnit : cotangentSheaf f ⟶
    (Scheme.Modules.pushforward a).obj (pullbackCotangentSheaf f a) :=
  (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app (cotangentSheaf f)

/-- The component at `W` of the unit `Ω_{X/S} ⟶ a_* a^* Ω_{X/S}`, read as a map
`Γ(Ω_{X/S}, W) ⟶ Γ(a^*Ω_{X/S}, a ⁻¹ᵁ W)` on sections. -/
noncomputable def pullbackCotangentUnitApp :
    Γ(cotangentSheaf f, W) ⟶ Γ(pullbackCotangentSheaf f a, a ⁻¹ᵁ W) :=
  (pullbackCotangentUnit f a).app W

/-- The component of the unit is semilinear over `a^♯ : Γ(X, W) ⟶ Γ(T, a ⁻¹ᵁ W)`. -/
theorem pullbackCotangentUnitApp_smul (b : Γ(X, W)) (y : Γ(cotangentSheaf f, W)) :
    (pullbackCotangentUnitApp f a W).hom (b • y)
      = (a.app W).hom b • (pullbackCotangentUnitApp f a W).hom y :=
  Scheme.Modules.Hom.app_smul (pullbackCotangentUnit f a) b y

/-- The pullback along `a` of the universal differential of a section of `𝒪_X` over `W`,
restricted to an open `U` of `T` mapping into `W`. -/
noncomputable def pullbackD (hUW : U ≤ a ⁻¹ᵁ W) :
    Γ(X, W) →+ Γ(pullbackCotangentSheaf f a, U) :=
  (((pullbackCotangentSheaf f a).presheaf.map (homOfLE hUW).op).hom.comp
    (pullbackCotangentUnitApp f a W).hom).comp (universalD f W)

/-- `pullbackD` is the universal differential followed by the unit of `a^* ⊣ a_*` and
restriction of sections. -/
theorem pullbackD_apply (hUW : U ≤ a ⁻¹ᵁ W) (b : Γ(X, W)) :
    pullbackD f a W hUW b
      = ((pullbackCotangentSheaf f a).presheaf.map (homOfLE hUW).op).hom
          ((pullbackCotangentUnitApp f a W).hom (universalD f W b)) :=
  rfl

/-- The Leibniz rule for `pullbackD`, with the action of `Γ(X, W)` on sections of `a^*Ω_{X/S}`
written out as the action of `Γ(T, U)` through `a.appLE W U`. -/
theorem pullbackD_mul' (hUW : U ≤ a ⁻¹ᵁ W) (b₁ b₂ : Γ(X, W)) :
    pullbackD f a W hUW (b₁ * b₂)
      = (a.appLE W U hUW).hom b₁ • pullbackD f a W hUW b₂
        + (a.appLE W U hUW).hom b₂ • pullbackD f a W hUW b₁ := by
  rw [pullbackD_apply, universalD_mul, map_add, pullbackCotangentUnitApp_smul,
    pullbackCotangentUnitApp_smul, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul]
  rfl

/-- The Leibniz rule for `pullbackD`, for the `Γ(X, W)`-module structure on sections of
`a^*Ω_{X/S}` given by `Stacks.Smooth.moduleAppLE`. -/
theorem pullbackD_mul (hUW : U ≤ a ⁻¹ᵁ W) (b₁ b₂ : Γ(X, W)) :
    letI := moduleAppLE a (pullbackCotangentSheaf f a) hUW
    pullbackD f a W hUW (b₁ * b₂)
      = b₁ • pullbackD f a W hUW b₂ + b₂ • pullbackD f a W hUW b₁ :=
  pullbackD_mul' f a W hUW b₁ b₂

/-- The pullback of the universal differential of the unit section vanishes. -/
theorem pullbackD_one (hUW : U ≤ a ⁻¹ᵁ W) : pullbackD f a W hUW 1 = 0 := by
  rw [pullbackD_apply, universalD_one, map_zero, map_zero]

/-- The pullback of the universal differential of a section coming from `𝒪_S` vanishes. -/
theorem pullbackD_appLE (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) (r : Γ(S, V)) :
    pullbackD f a W hUW ((f.appLE V W hWV).hom r) = 0 := by
  rw [pullbackD_apply, universalD_appLE f W hWV r, map_zero, map_zero]

/-- Restriction of sections is compatible with `pullbackD`. -/
theorem map_pullbackD (hUW : U ≤ a ⁻¹ᵁ W) (hU'W : U' ≤ a ⁻¹ᵁ W) (hU'U : U' ≤ U)
    (b : Γ(X, W)) :
    ((pullbackCotangentSheaf f a).presheaf.map (homOfLE hU'U).op).hom
        (pullbackD f a W hUW b) = pullbackD f a W hU'W b := by
  rw [pullbackD_apply, pullbackD_apply, ← Functor.map_comp_apply]
  rfl

/-- **The pullback of the universal derivation.** The universal derivation of `Ω_{X/S}`, pulled
back along `a : T ⟶ X` and restricted to an open `U` of `T` mapping into `W`, is a derivation of
`Γ(X, W)` over `Γ(S, V)` with values in `Γ(a^*Ω_{X/S}, U)`. -/
noncomputable def pullbackCotangentDerivation (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := moduleAppLE a (pullbackCotangentSheaf f a) hUW
    letI := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
    Derivation Γ(S, V) Γ(X, W) Γ(pullbackCotangentSheaf f a, U) :=
  letI := algebraAppLE f hWV
  letI := moduleAppLE a (pullbackCotangentSheaf f a) hUW
  letI := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  { toFun := pullbackD f a W hUW
    map_add' := map_add _
    map_smul' := fun r b ↦ by
      rw [Algebra.smul_def, pullbackD_mul f a W hUW, RingHom.algebraMap_toAlgebra,
        pullbackD_appLE f a W hWV hUW r, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := pullbackD_one f a W hUW
    leibniz' := pullbackD_mul f a W hUW }

/-- The underlying map of `pullbackCotangentDerivation` is `pullbackD`. -/
@[simp]
theorem pullbackCotangentDerivation_apply (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W)
    (b : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := moduleAppLE a (pullbackCotangentSheaf f a) hUW
    letI := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
    pullbackCotangentDerivation f a W hWV hUW b = pullbackD f a W hUW b :=
  rfl

end Derivation

/-! ### The comparison map -/

section Comparison

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (W : X.Opens) {V : S.Opens}
  {U U' : T.Opens}

/-- **The affine comparison map for `Ω_{X/S}`.** Writing `R = Γ(S, V)`, `B = Γ(X, W)` and
`A = Γ(T, U)`, this is the `A`-linear map `A ⊗[B] Ω[B⁄R] ⟶ Γ(a^*Ω_{X/S}, U)` carrying `x ⊗ d b`
to `x` times the pullback of the universal differential of `b`.

The content of the affine computation of [Stacks Project, Tag 01UM] is that this map is
bijective when `V` and `W` are affine opens and `T` is affine with `U = ⊤`; that is
`Stacks.Smooth.bijective_cotangentComparison`, proved in
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentBijective` rather than here. -/
noncomputable def cotangentComparison (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    Γ(T, U) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)] →ₗ[Γ(T, U)] Γ(pullbackCotangentSheaf f a, U) :=
  letI := algebraAppLE f hWV
  letI := algebraAppLE a hUW
  letI := moduleAppLE a (pullbackCotangentSheaf f a) hUW
  letI := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  letI := isScalarTowerAppLE a (pullbackCotangentSheaf f a) hUW
  letI := isScalarTowerAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  LinearMap.liftBaseChange Γ(T, U)
    (pullbackCotangentDerivation f a W hWV hUW).liftKaehlerDifferential

/-- The value of the comparison map on a generator. -/
theorem cotangentComparison_tmul_D (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) (x : Γ(T, U))
    (b : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    cotangentComparison f a W hWV hUW (x ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b)
      = x • pullbackD f a W hUW b := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  let := moduleAppLE a (pullbackCotangentSheaf f a) hUW
  let := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  let := isScalarTowerAppLE a (pullbackCotangentSheaf f a) hUW
  let := isScalarTowerAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  rw [cotangentComparison, LinearMap.liftBaseChange_tmul,
    Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- **The characterizing property of the comparison map.** It carries `1 ⊗ d b` to the pullback
of the universal differential of `b`. -/
@[simp]
theorem cotangentComparison_one_tmul_D (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) (b : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    cotangentComparison f a W hWV hUW (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b)
      = pullbackD f a W hUW b :=
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  (cotangentComparison_tmul_D f a W hWV hUW 1 b).trans (one_smul _ _)

/-- **Uniqueness of the comparison map.** A `Γ(T, U)`-linear map out of `A ⊗[B] Ω[B⁄R]` carrying
`1 ⊗ d b` to the pullback of the universal differential of `b` is the comparison map. -/
theorem cotangentComparison_unique (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    ∀ φ : Γ(T, U) ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)] →ₗ[Γ(T, U)]
        Γ(pullbackCotangentSheaf f a, U),
      (∀ b : Γ(X, W),
          φ (1 ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b) = pullbackD f a W hUW b) →
        φ = cotangentComparison f a W hWV hUW := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  let := moduleAppLE a (pullbackCotangentSheaf f a) hUW
  let := moduleAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  let := isScalarTowerAppLE a (pullbackCotangentSheaf f a) hUW
  let := isScalarTowerAppLEBase f a (pullbackCotangentSheaf f a) hWV hUW
  intro φ hφ
  apply (LinearMap.liftBaseChangeEquiv Γ(T, U)).symm.injective
  rw [cotangentComparison, LinearEquiv.symm_apply_apply]
  refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b ↦ ?_)
  exact (hφ b).trans (Derivation.liftKaehlerDifferential_comp_D
    (pullbackCotangentDerivation f a W hWV hUW) b).symm

/-- **Naturality of the comparison map.** Restricting sections from `U` to a smaller open `U'`
corresponds to base change along the restriction map `Γ(T, U) ⟶ Γ(T, U')`. For `T` affine,
`U = ⊤` and `U' = T.basicOpen g` this is the naturality with respect to restriction to the basic
opens of `T`. -/
theorem map_cotangentComparison (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) (hU'W : U' ≤ a ⁻¹ᵁ W)
    (hU'U : U' ≤ U) (x : Γ(T, U)) (b : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    letI := algebraAppLE a hU'W
    ((pullbackCotangentSheaf f a).presheaf.map (homOfLE hU'U).op).hom
        (cotangentComparison f a W hWV hUW (x ⊗ₜ KaehlerDifferential.D Γ(S, V) Γ(X, W) b))
      = cotangentComparison f a W hWV hU'W
          ((T.presheaf.map (homOfLE hU'U).op).hom x ⊗ₜ
            KaehlerDifferential.D Γ(S, V) Γ(X, W) b) := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  let := algebraAppLE a hU'W
  rw [cotangentComparison_tmul_D, cotangentComparison_tmul_D, Scheme.Modules.map_smul,
    map_pullbackD f a W hUW hU'W hU'U b]

end Comparison

/-! ### Localization of the base-change side -/

/-- The base-change side of the naturality square localizes: for `g` a global section of an
affine `T`, the map `Γ(T, ⊤) ⊗[B] Ω[B⁄R] ⟶ Γ(T, T.basicOpen g) ⊗[B] Ω[B⁄R]` is a localization
away from `g`. This is what turns the differences of two local lifts in the proof of
[Stacks Project, Tag 02H6] into a Čech cochain. -/
theorem isLocalizedModule_rTensor_basicOpen {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X)
    [IsAffine T] (W : X.Opens) {V : S.Opens} (hWV : W ≤ f ⁻¹ᵁ V)
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (g : Γ(T, ⊤)) (hU'W : T.basicOpen g ≤ a ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE a hUW
    letI := algebraAppLE a hU'W
    haveI : IsScalarTower Γ(X, W) Γ(T, ⊤) Γ(T, T.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq fun c ↦ congr($((a.appLE_map hUW
        (homOfLE (T.basicOpen_le g)).op).symm).hom c)
    IsLocalizedModule.Away g (TensorProduct.AlgebraTensorModule.rTensor Γ(X, W)
      Ω[Γ(X, W)⁄Γ(S, V)] (Algebra.linearMap Γ(T, ⊤) Γ(T, T.basicOpen g))) := by
  let := algebraAppLE f hWV
  let := algebraAppLE a hUW
  let := algebraAppLE a hU'W
  infer_instance

end Stacks.Smooth

end
