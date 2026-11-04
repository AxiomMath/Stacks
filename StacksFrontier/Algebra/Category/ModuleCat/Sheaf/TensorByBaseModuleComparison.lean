module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorByBaseModuleOfHomLinearIso

/-!
# The canonical comparison out of `𝓕 ⊗_R M`

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it, let `R` be a commutative
ring, let `θ : constantRingPresheaf R ⟶ O` be a morphism of presheaves of commutative rings and
let `𝓕` be a sheaf of `O`-modules.  `Stacks.TensorByBaseModule.tensorByBaseModulePresheafOfHom`
is then the presheaf of `O`-modules

  `U ↦ 𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)`

whose sheafification is `Stacks.TensorByBaseModule.tensorByBaseModuleOfHom`, the functor
`M ↦ 𝓕 ⊗_R M`.  This file builds the canonical comparison *out of* that presheaf into a given
presheaf of `O`-modules `N`, and feeds it to the gluing step of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorByBaseModuleOfHomLinearIso.lean`.

**The data the comparison consumes.**  A morphism of presheaves of `O`-modules out of
`𝓕 ⊗_{O} (O ⊗_R M)` is the same thing as an `R`-linear map from `M` to the `O`-module
morphisms `𝓕 ⟶ N`: that is the universal property of the two tensor products, and it is what
`Stacks.TensorByBaseModule.comparison` takes as input, in the form of a family
`σ : M → (𝓕.val ⟶ N)` additive in `M` and carrying `r • m` to `θ(r)` times `σ m`.  The
comparison it produces is

  `x ⊗ (a ⊗ m) ↦ a • (σ m)_U x`.

This is the shape in which the second part of [Stacks Project, Tag 073K] glues: there `N` is the
direct image `g'_*ℱ'` along the base change of a flat morphism of affine bases, `M` is the
coordinate ring of the new base, and `σ m` is multiplication by `m` composed with the unit of the
pullback-pushforward adjunction, which is a morphism of `𝒪_X`-modules because the direct image is
a module over the direct image of the structure sheaf of `X'`.

**What the gluing step then needs.**  Only bijectivity of the comparison on the sections over the
objects of a family whose arrows generate covering sieves —
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfBijectiveAppOfHom` reduces local bijectivity to
that, through `Stacks.Presheaf.isLocallyInjective_of_injective_app` and
`Stacks.Presheaf.isLocallySurjective_of_surjective_app`.  On the small étale site of an algebraic
space the family is the affine charts; see
`StacksFrontier/AlgebraicGeometry/Spaces/TensorByBaseModuleAffineChartComparison.lean`.

## Main definitions

* `Stacks.TensorByBaseModule.comparisonFiber`: for a section `x` of `𝓕` over `U`, the `R`-linear
  map `m ↦ (σ m)_U x`.
* `Stacks.TensorByBaseModule.comparisonBilin`: that family read as an `O(U)`-linear map from
  `𝓕(U)` to the `R`-linear maps out of `M`, which is the bilinear datum the two tensor products
  consume.
* `Stacks.TensorByBaseModule.comparisonApp`: the component of the comparison over one object.
* `Stacks.TensorByBaseModule.comparison`: **the canonical comparison
  `𝓕 ⊗_{O} (O ⊗_R M) ⟶ N`.**
* `Stacks.TensorByBaseModule.comparisonCancelled`: the comparison over an object read after
  cancelling the base change, as the map `𝓕(U) ⊗_R M → N(U)`, `x ⊗ m ↦ (σ m)_U x`.
* `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfComparisonOfHom`,
  `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfLocallyBijectiveOfHom` and
  `Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfComparison`: **the comparison fed to the
  gluing step**, in the form taking a morphism of presheaves of rings and in the form taking a
  terminal object of the site and a ring homomorphism into its sections.

## Main results

* `Stacks.TensorByBaseModule.comparisonApp_tmul`: the comparison sends the generator
  `x ⊗ (a ⊗ m)` to `a • (σ m)_U x`.  This is the formula a consumer checks bijectivity against.
* `Stacks.TensorByBaseModule.comparisonApp_naturality`: the components commute with restriction.
* `Stacks.TensorByBaseModule.addHom_ext_tmul_tmul`: two additive maps out of
  `F ⊗_A (A ⊗_R M)` agree as soon as they agree on the generators.
* `Stacks.TensorByBaseModule.comparisonApp_eq_cancelBaseChange` and
  `Stacks.TensorByBaseModule.bijective_comparisonApp_iff`: **the comparison is bijective over an
  object exactly when the map `𝓕(U) ⊗_R M → N(U)` is**, the two differing by the cancellation of
  the base change — which is `Stacks.TensorByBaseModule.sectionsEquivOfHom`.  This is the form in
  which the chart-wise input of the gluing arrives.

## Implementation notes

*Why the hypotheses on `σ` are stated on sections and not on morphisms.*  Additivity of `σ` and
its compatibility with scalars read most briefly as equalities of morphisms of presheaves of
modules, `σ (m₁ + m₂) = σ m₁ + σ m₂` and
`σ (r • m) = σ m ≫ Stacks.TensorByBaseModule.presheafMultOfHom R O θ r N`.  They are stated
instead on the sections over each object, because the first spelling needs the additive structure
on a hom type of presheaves of modules and therefore needs the indexing presheaf of rings to be
*syntactically* of the form `O ⋙ forget₂ CommRingCat RingCat`.  A geometric consumer reaches the
structure sheaf of the small étale site through
`AlgebraicGeometry.Space.smallEtaleRingSheaf`, which is
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj O` and is that shape only after unfolding
`CategoryTheory.sheafCompose`; instance search does not unfold it, and the additive structure is
not found.  The sectionwise form has no such need.

*Where the two universal properties are discharged.*  The inner one is
`LinearMap.liftBaseChangeEquiv`, which turns an `R`-linear map `M →ₗ[R] N(U)` into an
`O(U)`-linear map `O(U) ⊗_R M →ₗ[O(U)] N(U)` and is an `O(U)`-linear equivalence, so the
additivity and the `O(U)`-linearity of `comparisonApp` in the `𝓕(U)` variable follow from those
of `comparisonBilin` with no computation on tensors.  The outer one is `TensorProduct.lift`.

*Why naturality is proved through `addHom_ext_tmul_tmul` and an explicit additive map.*  The
sections of `tensorByBaseModulePresheafOfHom` over `U` are the tensor product
`𝓕(U) ⊗_{O(U)} (O(U) ⊗_R M)` by `rfl`, but the module instances the monoidal structure of
`PresheafOfModules` puts on that tensor product are indexed by the ring of sections read through
`CategoryTheory.forget₂ CommRingCat RingCat`, and are not the ones instance search finds for the
spelling above.  So `TensorProduct.tmul_zero` and `TensorProduct.tmul_add` do not *rewrite* in a
goal obtained by `TensorProduct.ext'` from the naturality square, even though they hold of it.
`Stacks.TensorByBaseModule.comparisonApp_naturality` therefore states naturality for an element
of the tensor product written in the spelling whose instances are the canonical ones, packages
the two sides as additive maps out of it, and compares them with
`Stacks.TensorByBaseModule.addHom_ext_tmul_tmul`; `Stacks.TensorByBaseModule.comparison` then
quotes it, the two spellings being definitionally equal.

No declaration here carries a `stacks` tag.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite Limits MonoidalCategory TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe v u w

namespace Stacks.TensorByBaseModule

variable {C : Type u} [Category.{v} C]

/-- Two additive maps out of `F ⊗_A (A ⊗_R M)` agree as soon as they agree on the generators
`x ⊗ (a ⊗ m)`. -/
theorem addHom_ext_tmul_tmul {Rr Aa F Mm P : Type*} [CommRing Rr] [CommRing Aa] [Algebra Rr Aa]
    [AddCommGroup F] [Module Aa F] [AddCommGroup Mm] [Module Rr Mm] [AddCommGroup P]
    {g h : (F ⊗[Aa] (Aa ⊗[Rr] Mm)) →+ P}
    (H : ∀ x a m, g (x ⊗ₜ[Aa] (a ⊗ₜ[Rr] m)) = h (x ⊗ₜ[Aa] (a ⊗ₜ[Rr] m))) : g = h := by
  refine AddMonoidHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul x u =>
    induction u using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add p q hp hq => rw [TensorProduct.tmul_add, map_add, map_add, hp, hq]
    | tmul a m => exact H x a m

section Comparison

/-- Two additive maps out of `F ⊗_A (A ⊗_R M)` agree pointwise as soon as they agree on the
generators `x ⊗ (a ⊗ m)`. -/
private theorem addHom_apply_eq_of_tmul_tmul {Rr Aa F Mm P : Type*} [CommRing Rr] [CommRing Aa]
    [Algebra Rr Aa] [AddCommGroup F] [Module Aa F] [AddCommGroup Mm] [Module Rr Mm]
    [AddCommGroup P] {g h : (F ⊗[Aa] (Aa ⊗[Rr] Mm)) →+ P}
    (H : ∀ x a m, g (x ⊗ₜ[Aa] (a ⊗ₜ[Rr] m)) = h (x ⊗ₜ[Aa] (a ⊗ₜ[Rr] m)))
    (t : F ⊗[Aa] (Aa ⊗[Rr] Mm)) : g t = h t :=
  DFunLike.congr_fun (addHom_ext_tmul_tmul H) t

variable (R : Type w) [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})
  (𝓕 : SheafOfModules.{w} (ringSheaf J O)) (θ : constantRingPresheaf (C := C) R ⟶ O.val)
  (M : ModuleCat.{w} R) (N : PMod O.val) (σ : M → (𝓕.val ⟶ N))
  (hadd : ∀ (m₁ m₂ : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
    ((σ (m₁ + m₂)).app X).hom x = ((σ m₁).app X).hom x + ((σ m₂).app X).hom x)
  (hsmul : ∀ (r : R) (m : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
    ((σ (r • m)).app X).hom x = ((θ.app X).hom r) • ((σ m).app X).hom x)

include hadd hsmul

/-- For a section `x` of `𝓕` over `X`, the `R`-linear map `m ↦ (σ m)_X x`. -/
def comparisonFiber (X : Cᵒᵖ) (x : 𝓕.val.obj X) :
    letI := sectionsModuleOfHom R J O θ N X
    M →ₗ[R] N.obj X :=
  letI := sectionsModuleOfHom R J O θ N X
  { toFun m := ((σ m).app X).hom x
    map_add' m₁ m₂ := hadd m₁ m₂ X x
    map_smul' r m := hsmul r m X x }

/-- The bilinear datum of the comparison over an object `X`: the `O(X)`-linear map carrying a
section `x` of `𝓕` to the `R`-linear map `m ↦ (σ m)_X x`.  It is `O(X)`-linear in `x` because
each `σ m` is a morphism of presheaves of `O`-modules. -/
def comparisonBilin (X : Cᵒᵖ) :
    letI := coefficientAlgebraOfHom R J O θ X
    letI := sectionsModuleOfHom R J O θ N X
    letI := isScalarTowerOfHom R J O θ N X
    𝓕.val.obj X →ₗ[O.val.obj X] (M →ₗ[R] N.obj X) :=
  letI := coefficientAlgebraOfHom R J O θ X
  letI := sectionsModuleOfHom R J O θ N X
  letI := isScalarTowerOfHom R J O θ N X
  { toFun x := comparisonFiber R J O 𝓕 θ M N σ hadd hsmul X x
    map_add' x y := LinearMap.ext fun m => map_add ((σ m).app X).hom x y
    map_smul' a x := LinearMap.ext fun m => ((σ m).app X).hom.map_smul a x }

/-- **The component of the comparison over an object**: the `O(X)`-linear map
`𝓕(X) ⊗_{O(X)} (O(X) ⊗_R M) ⟶ N(X)` sending `x ⊗ (a ⊗ m)` to `a • (σ m)_X x`.

The inner tensor product is discharged by `LinearMap.liftBaseChangeEquiv`, an `O(X)`-linear
equivalence, so that `comparisonBilin` composed with it is `O(X)`-linear in `x` with no
computation on tensors; the outer one by `TensorProduct.lift`. -/
def comparisonApp (X : Cᵒᵖ) :
    ((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M).obj X ⟶ N.obj X :=
  letI := coefficientAlgebraOfHom R J O θ X
  letI := sectionsModuleOfHom R J O θ N X
  letI := isScalarTowerOfHom R J O θ N X
  ModuleCat.ofHom (TensorProduct.lift
    ((LinearMap.liftBaseChangeEquiv (R := R) (M := M) (N := N.obj X)
      (O.val.obj X)).toLinearMap ∘ₗ comparisonBilin R J O 𝓕 θ M N σ hadd hsmul X))

/-- **The comparison on a generator**: `x ⊗ (a ⊗ m) ↦ a • (σ m)_X x`.  The source is written in
the spelling of `Stacks.TensorByBaseModule.tensorByBaseModulePresheafOfHom_obj_obj`, which is
the sections of the presheaf-level tensor product by `rfl`. -/
theorem comparisonApp_tmul (X : Cᵒᵖ) (x : 𝓕.val.obj X) (a : O.val.obj X) (m : M) :
    letI := coefficientAlgebraOfHom R J O θ X
    (comparisonApp R J O 𝓕 θ M N σ hadd hsmul X).hom
        ((x ⊗ₜ[O.val.obj X] (a ⊗ₜ[R] m) :
          𝓕.val.obj X ⊗[O.val.obj X] (O.val.obj X ⊗[R] M)))
      = a • ((σ m).app X).hom x :=
  rfl

/-- **The components commute with restriction**, stated for a section written in the closed
form `𝓕(X) ⊗_{O(X)} (O(X) ⊗_R M)`: on a generator both sides are
`O(f)(a) • (σ m)_Y (𝓕(f) x)`, the left by the restriction maps of the two tensor factors and the
right by semilinearity of the restriction maps of `N` together with naturality of `σ m`. -/
theorem comparisonApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI := coefficientAlgebraOfHom R J O θ X
    ∀ t : 𝓕.val.obj X ⊗[O.val.obj X] (O.val.obj X ⊗[R] M),
      (comparisonApp R J O 𝓕 θ M N σ hadd hsmul Y).hom
          ((((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M).map f).hom t)
        = (N.map f).hom ((comparisonApp R J O 𝓕 θ M N σ hadd hsmul X).hom t) := by
  let := coefficientAlgebraOfHom R J O θ X
  refine addHom_apply_eq_of_tmul_tmul
    (g := ((comparisonApp R J O 𝓕 θ M N σ hadd hsmul Y).hom.toAddMonoidHom.comp
      (((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M).map f).hom.toAddMonoidHom :
        (𝓕.val.obj X ⊗[O.val.obj X] (O.val.obj X ⊗[R] M)) →+ N.obj Y))
    (h := (N.map f).hom.toAddMonoidHom.comp
      (comparisonApp R J O 𝓕 θ M N σ hadd hsmul X).hom.toAddMonoidHom) fun x a m => ?_
  show (comparisonApp R J O 𝓕 θ M N σ hadd hsmul Y).hom
      ((((tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M).map f).hom
        ((x ⊗ₜ[O.val.obj X] (a ⊗ₜ[R] m) :
          𝓕.val.obj X ⊗[O.val.obj X] (O.val.obj X ⊗[R] M))))
    = (N.map f).hom (a • ((σ m).app X).hom x)
  rw [PresheafOfModules.map_smul, ← PresheafOfModules.naturality_apply (σ m) f x]
  rfl

/-- **The canonical comparison `𝓕 ⊗_{O} (O ⊗_R M) ⟶ N`** attached to a family
`σ : M → (𝓕 ⟶ N)` that is additive and carries `r • m` to `θ(r)` times `σ m`.  Over an object it
is `x ⊗ (a ⊗ m) ↦ a • (σ m)_U x`; see `Stacks.TensorByBaseModule.comparisonApp_tmul`. -/
def comparison : (tensorByBaseModulePresheafOfHom R J O 𝓕 θ).obj M ⟶ N where
  app X := comparisonApp R J O 𝓕 θ M N σ hadd hsmul X
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    exact comparisonApp_naturality R J O 𝓕 θ M N σ hadd hsmul f t

/-- The comparison acts over an object by `Stacks.TensorByBaseModule.comparisonApp`. -/
@[simp]
theorem comparison_app (X : Cᵒᵖ) :
    (comparison R J O 𝓕 θ M N σ hadd hsmul).app X
      = comparisonApp R J O 𝓕 θ M N σ hadd hsmul X :=
  rfl

/-- **The comparison read after cancelling the base change**: the `R`-balanced map
`𝓕(X) ⊗_R M ⟶ N(X)` sending `x ⊗ m` to `(σ m)_X x`.  This is the form in which a consumer
checks bijectivity over an object, the sections of the presheaf-level tensor product being
`𝓕(X) ⊗_R M` by `Stacks.TensorByBaseModule.sectionsEquivOfHom`. -/
def comparisonCancelled (X : Cᵒᵖ) :
    letI := sectionsModuleOfHom R J O θ 𝓕.val X
    letI := sectionsModuleOfHom R J O θ N X
    (𝓕.val.obj X ⊗[R] M) →ₗ[R] N.obj X :=
  letI := sectionsModuleOfHom R J O θ 𝓕.val X
  letI := sectionsModuleOfHom R J O θ N X
  TensorProduct.lift
    { toFun x := comparisonFiber R J O 𝓕 θ M N σ hadd hsmul X x
      map_add' x y := LinearMap.ext fun m => map_add ((σ m).app X).hom x y
      map_smul' _r x := LinearMap.ext fun m => ((σ m).app X).hom.map_smul _ x }

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `Stacks.TensorByBaseModule.comparisonCancelled` on a generator. -/
theorem comparisonCancelled_tmul (X : Cᵒᵖ) (x : 𝓕.val.obj X) (m : M) :
    letI := sectionsModuleOfHom R J O θ 𝓕.val X
    comparisonCancelled R J O 𝓕 θ M N σ hadd hsmul X (x ⊗ₜ[R] m) = ((σ m).app X).hom x :=
  rfl

/-- **The comparison factors through the cancellation of the base change.**  The cancellation is
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which is what
`Stacks.TensorByBaseModule.sectionsEquivOfHom` is by definition. -/
theorem comparisonApp_eq_cancelBaseChange (X : Cᵒᵖ) :
    letI := coefficientAlgebraOfHom R J O θ X
    letI := sectionsModuleOfHom R J O θ 𝓕.val X
    letI := sectionsModuleOfHom R J O θ N X
    letI := isScalarTowerOfHom R J O θ 𝓕.val X
    ∀ t : 𝓕.val.obj X ⊗[O.val.obj X] (O.val.obj X ⊗[R] M),
      comparisonCancelled R J O 𝓕 θ M N σ hadd hsmul X
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R (O.val.obj X) (O.val.obj X)
            (𝓕.val.obj X) M t)
        = (comparisonApp R J O 𝓕 θ M N σ hadd hsmul X).hom t := by
  let := coefficientAlgebraOfHom R J O θ X
  let := sectionsModuleOfHom R J O θ 𝓕.val X
  let := sectionsModuleOfHom R J O θ N X
  let := isScalarTowerOfHom R J O θ 𝓕.val X
  refine addHom_apply_eq_of_tmul_tmul
    (g := (comparisonCancelled R J O 𝓕 θ M N σ hadd hsmul X).toAddMonoidHom.comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (O.val.obj X) (O.val.obj X)
        (𝓕.val.obj X) M).toLinearMap.toAddMonoidHom)
    (h := (comparisonApp R J O 𝓕 θ M N σ hadd hsmul X).hom.toAddMonoidHom) fun x a m => ?_
  show ((σ m).app X).hom (a • x) = a • ((σ m).app X).hom x
  exact ((σ m).app X).hom.map_smul a x

/-- **The comparison is bijective over an object exactly when its cancelled form is.**  This is
the reduction a consumer uses: bijectivity of the comparison over an object is bijectivity of the
map `𝓕(X) ⊗_R M → N(X)`, `x ⊗ m ↦ (σ m)_X x`. -/
theorem bijective_comparisonApp_iff (X : Cᵒᵖ) :
    letI := sectionsModuleOfHom R J O θ 𝓕.val X
    letI := sectionsModuleOfHom R J O θ N X
    Function.Bijective (comparisonApp R J O 𝓕 θ M N σ hadd hsmul X).hom
      ↔ Function.Bijective (comparisonCancelled R J O 𝓕 θ M N σ hadd hsmul X) := by
  let := coefficientAlgebraOfHom R J O θ X
  let := sectionsModuleOfHom R J O θ 𝓕.val X
  let := sectionsModuleOfHom R J O θ N X
  let := isScalarTowerOfHom R J O θ 𝓕.val X
  rw [← funext (comparisonApp_eq_cancelBaseChange R J O 𝓕 θ M N σ hadd hsmul X)]
  exact Equiv.bijective_comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (O.val.obj X) (O.val.obj X)
      (𝓕.val.obj X) M).toEquiv _

end Comparison


section Gluing

variable (R : Type w) [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (𝓕 : SheafOfModules.{w} (ringSheaf J O)) (θ : constantRingPresheaf (C := C) R ⟶ O.val)
  (M : ModuleCat.{w} R) (G : SheafOfModules.{w} (ringSheaf J O))
  (σ : M → (𝓕.val ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
    ((SheafOfModules.forget (ringSheaf J O)).obj G)))
  (hadd : ∀ (m₁ m₂ : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
    ((σ (m₁ + m₂)).app X).hom x = ((σ m₁).app X).hom x + ((σ m₂).app X).hom x)
  (hsmul : ∀ (r : R) (m : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
    ((σ (r • m)).app X).hom x = ((θ.app X).hom r) • ((σ m).app X).hom x)

include hadd hsmul

/-- **`𝓕 ⊗_R M ≅ G` from the canonical comparison, bijective over a covering family.**  A sheaf
of `O`-modules receiving a comparison from `σ` that is bijective on the sections over the objects
of a family whose arrows generate covering sieves *is* the value of
`Stacks.TensorByBaseModule.tensorByBaseModuleOfHom` at `M`. -/
noncomputable def tensorByBaseModuleIsoOfComparisonOfHom
    (P : C → Prop)
    (hcov : ∀ X : C, Sieve.generate (fun {W : C} (_ : W ⟶ X) => P W) ∈ J X)
    (hbij : ∀ W : C, P W →
      Function.Bijective (comparisonApp R J O 𝓕 θ M _ σ hadd hsmul (op W)).hom) :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).obj M ≅ G :=
  tensorByBaseModuleIsoOfBijectiveAppOfHom R J O 𝓕 θ M G
    (comparison R J O 𝓕 θ M _ σ hadd hsmul) P hcov hbij

/-- **`𝓕 ⊗_R M ≅ G` from a locally bijective canonical comparison**, the form of the gluing step
that takes the local bijectivity directly rather than through a covering family. -/
noncomputable def tensorByBaseModuleIsoOfLocallyBijectiveOfHom
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map
      (comparison R J O 𝓕 θ M _ σ hadd hsmul))]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf (ringSheaf J O).obj).map
      (comparison R J O 𝓕 θ M _ σ hadd hsmul))] :
    (tensorByBaseModuleOfHom R J O 𝓕 θ).obj M ≅ G :=
  tensorByBaseModuleIsoOfHom R J O 𝓕 θ M G (comparison R J O 𝓕 θ M _ σ hadd hsmul)

end Gluing

section GluingTerminal

variable (R : Type w) [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (O : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (𝓕 : SheafOfModules.{w} (ringSheaf J O)) {U₀ : C} (hU₀ : IsTerminal U₀)
  (α : R →+* O.val.obj (op U₀))
  (M : ModuleCat.{w} R) (G : SheafOfModules.{w} (ringSheaf J O))
  (σ : M → (𝓕.val ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj
    ((SheafOfModules.forget (ringSheaf J O)).obj G)))
  (hadd : ∀ (m₁ m₂ : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
    ((σ (m₁ + m₂)).app X).hom x = ((σ m₁).app X).hom x + ((σ m₂).app X).hom x)
  (hsmul : ∀ (r : R) (m : M) (X : Cᵒᵖ) (x : 𝓕.val.obj X),
    ((σ (r • m)).app X).hom x
      = (((coefficientMap R hU₀ (O := O.val) α).app X).hom r) • ((σ m).app X).hom x)

include hadd hsmul

/-- **`𝓕 ⊗_R M ≅ G` from the canonical comparison**, in the form taking a terminal object of the
site and a ring homomorphism into its sections. -/
noncomputable def tensorByBaseModuleIsoOfComparison
    (P : C → Prop)
    (hcov : ∀ X : C, Sieve.generate (fun {W : C} (_ : W ⟶ X) => P W) ∈ J X)
    (hbij : ∀ W : C, P W → Function.Bijective
      (comparisonApp R J O 𝓕 (coefficientMap R hU₀ (O := O.val) α) M _ σ hadd hsmul (op W)).hom) :
    (tensorByBaseModule R hU₀ J O 𝓕 α).obj M ≅ G :=
  tensorByBaseModuleIsoOfBijectiveApp R hU₀ J O 𝓕 α M G
    (comparison R J O 𝓕 (coefficientMap R hU₀ (O := O.val) α) M _ σ hadd hsmul) P hcov hbij

end GluingTerminal

end Stacks.TensorByBaseModule

end
