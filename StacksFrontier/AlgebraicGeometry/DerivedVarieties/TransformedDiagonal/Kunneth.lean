module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Terms
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorFunctorial

/-!
# The Hom identification behind the transformed resolution of the diagonal

Let `X` and `Y` be schemes over `Spec A`, let

`… → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0`

be a resolution of the diagonal of `X` by external tensor products of finite locally free
modules, and let `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`. The complex

`… → ℰ₂ ⊠ F(𝒢₂) → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)`

of [Stacks, Tag 0G0A] has for differentials those of the resolution, read through an
identification of the Hom group `Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)` with `Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))`.
This file constructs such an identification, compatible with identities and with composition,
from Künneth data on pure maps.

A pair of maps `a : ℰᵢ ⟶ ℰⱼ` and `b : 𝒢ᵢ ⟶ 𝒢ⱼ` of factors gives `a ⊠ b : ℰᵢ ⊠ 𝒢ᵢ ⟶ ℰⱼ ⊠ 𝒢ⱼ`
on `X ×_A X` and `a ⊠ F(b) : ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)` on `X ×_A Y`, and both assignments are
extended additively to formal integral combinations of such pairs. The Künneth data say that
both extensions are surjective and that they have the same kernel; the identification of Hom
groups is then the isomorphism of the two quotients.

## Main definitions

* `AlgebraicGeometry.derivedExternalTensorMap`: the map of derived external tensor products
  induced by a map on each factor.
* `AlgebraicGeometry.DiagonalResolution.secondFactorHomEquiv`: full faithfulness of `F`
  identifies `Hom(𝒢ᵢ, 𝒢ⱼ)` with `Hom(F(𝒢ᵢ), F(𝒢ⱼ))`.
* `AlgebraicGeometry.DiagonalResolution.transformedMap`: the pure map
  `a ⊠ F(b) : ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)`.
* `AlgebraicGeometry.DiagonalResolution.boxPairing` and
  `AlgebraicGeometry.DiagonalResolution.transformedPairing`: the additive extensions of
  `(a, b) ↦ a ⊠ b` and of `(a, b) ↦ a ⊠ F(b)` to formal integral combinations of pairs.
* `AlgebraicGeometry.DiagonalResolution.transformedImagePairing`: the same additive extension
  on `X ×_A Y`, indexed by pairs `(a, c)` with `c` a map between the *images* of the second
  factors.
* `AlgebraicGeometry.DiagonalResolution.KunnethHomData`: both pairings are surjective and they
  have the same kernel.
* `AlgebraicGeometry.DiagonalResolution.KunnethHomData.homTransport`: the transport of Hom
  groups determined by such data.
* `AlgebraicGeometry.DiagonalResolution.kunnethHomEquiv`: the identification of Hom groups
  determined by the two surjectivity statements, the equality of kernels and the full
  faithfulness of `F`.
* `AlgebraicGeometry.DiagonalResolution.kunnethComplex`: the complex
  `… → ℰ₂ ⊠ F(𝒢₂) → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)` of [Stacks, Tag 0G0A], built from that
  identification.

## Main results

* `AlgebraicGeometry.bifunctorMap_add_left`, `AlgebraicGeometry.bifunctorMap_add_right`,
  `AlgebraicGeometry.bifunctorMap_zero_left` and `AlgebraicGeometry.bifunctorMap_zero_right`: a
  bifunctor is additive in each variable separately, and vanishes on a zero map in either,
  whenever fixing the other variable gives an additive functor.
* `AlgebraicGeometry.derivedExternalTensorMap_add_left`,
  `AlgebraicGeometry.derivedExternalTensorMap_add_right`,
  `AlgebraicGeometry.derivedExternalTensorMap_zero_left` and
  `AlgebraicGeometry.derivedExternalTensorMap_zero_right`: **the derived external tensor
  product of maps is bi-additive**, and vanishes as soon as one of its two arguments does.
* `AlgebraicGeometry.DiagonalResolution.KunnethHomData.of`: Künneth data from the surjectivity
  of the box pairing and of the transformed image pairing, the equality of kernels, and the full
  faithfulness of `F`.
* `AlgebraicGeometry.DiagonalResolution.KunnethHomData.homEquiv_boxMap`: the constructed
  transport carries the pure map `a ⊠ b` to the pure map `a ⊠ F(b)`.
* `AlgebraicGeometry.DiagonalResolution.KunnethHomData.homTransport_complex_d`: the
  differentials of the complex of [Stacks, Tag 0G0A] built from the constructed transport.
* `AlgebraicGeometry.DiagonalResolution.surjective_transformedPairing`: for `F` fully faithful,
  surjectivity of the transformed image pairing gives surjectivity of the transformed pairing.
* `AlgebraicGeometry.DiagonalResolution.kunnethComplex_d`: the differentials of the complex of
  [Stacks, Tag 0G0A] are those of the resolution of the diagonal, read through the constructed
  identification of Hom groups.

## References

* [Stacks Project, Tag 0FXZ](https://stacks.math.columbia.edu/tag/0FXZ)
* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.PerfectComplexes

universe u

namespace AlgebraicGeometry

/-! ### Formal combinations of pure maps -/

section FreeAbelianGroup

variable {C : Type*} [Category C] [Preadditive C]

/-- **A formal combination of composable pairs is carried to the composite.** For two families
`pa` and `pb` of maps `Z₀ ⟶ Z₁` and `Z₁ ⟶ Z₂` indexed by `α` and `β`, and a pairing `m` of
indices whose value under a third family `pc` is the composite, the additive extension of `pc`
carries the convolution of two formal combinations to the composite of their values. -/
theorem freeAbelianGroup_lift_comp {Z₀ Z₁ Z₂ : C} {α β γ : Type*}
    (pa : α → (Z₀ ⟶ Z₁)) (pb : β → (Z₁ ⟶ Z₂)) (pc : γ → (Z₀ ⟶ Z₂)) (m : α → β → γ)
    (hm : ∀ a b, pc (m a b) = pa a ≫ pb b)
    (u : FreeAbelianGroup α) (v : FreeAbelianGroup β) :
    FreeAbelianGroup.lift pc (FreeAbelianGroup.lift
        (fun a => FreeAbelianGroup.lift (fun b => FreeAbelianGroup.of (m a b)) v) u) =
      FreeAbelianGroup.lift pa u ≫ FreeAbelianGroup.lift pb v := by
  induction u using FreeAbelianGroup.induction_on with
  | zero => simp
  | of a =>
    simp only [FreeAbelianGroup.lift_apply_of]
    induction v using FreeAbelianGroup.induction_on with
    | zero => simp
    | of b => simp only [FreeAbelianGroup.lift_apply_of, hm]
    | neg b hb => simp only [map_neg, Preadditive.comp_neg, hb]
    | add x y hx hy => simp only [map_add, Preadditive.comp_add, hx, hy]
  | neg a ha => simp only [map_neg, Preadditive.neg_comp, ha]
  | add x y hx hy => simp only [map_add, Preadditive.add_comp, hx, hy]

end FreeAbelianGroup

/-! ### Functoriality of a bifunctor in both variables at once -/

section Bifunctor

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] (T : C₁ ⥤ C₂ ⥤ D)

/-- The map `(T.obj K).obj L ⟶ (T.obj K').obj L'` that a bifunctor `T` induces from a map in
each of its two variables. -/
def bifunctorMap {K K' : C₁} {L L' : C₂} (u : K ⟶ K') (v : L ⟶ L') :
    (T.obj K).obj L ⟶ (T.obj K').obj L' :=
  (T.map u).app L ≫ (T.obj K').map v

/-- **A bifunctor carries a pair of identities to the identity.** -/
@[simp]
theorem bifunctorMap_id (K : C₁) (L : C₂) :
    bifunctorMap T (𝟙 K) (𝟙 L) = 𝟙 ((T.obj K).obj L) := by
  rw [bifunctorMap, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.comp_id]

/-- **A bifunctor carries composites to composites in both variables at once.** -/
theorem bifunctorMap_comp {K K' K'' : C₁} {L L' L'' : C₂} (u : K ⟶ K') (u' : K' ⟶ K'')
    (v : L ⟶ L') (v' : L' ⟶ L'') :
    bifunctorMap T u v ≫ bifunctorMap T u' v' = bifunctorMap T (u ≫ u') (v ≫ v') := by
  dsimp only [bifunctorMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    Category.assoc, Category.assoc, ← Category.assoc ((T.obj K').map v),
    (T.map u').naturality v, Category.assoc]

end Bifunctor

/-! ### Bi-additivity of a bifunctor on morphisms -/

section BifunctorAdditive

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] [Preadditive C₁]
  [Preadditive C₂] [Preadditive D] (T : C₁ ⥤ C₂ ⥤ D)

omit [Preadditive C₂] in
/-- **A bifunctor is additive in its first variable**, as soon as fixing the second gives an
additive functor. -/
theorem bifunctorMap_add_left {K K' : C₁} {L L' : C₂} (u u' : K ⟶ K') (v : L ⟶ L')
    [(T.flip.obj L).Additive] :
    bifunctorMap T (u + u') v = bifunctorMap T u v + bifunctorMap T u' v := by
  have h : (T.map (u + u')).app L = (T.map u).app L + (T.map u').app L :=
    (T.flip.obj L).map_add
  dsimp only [bifunctorMap]
  rw [h, Preadditive.add_comp]

omit [Preadditive C₁] in
/-- **A bifunctor is additive in its second variable**, as soon as fixing the first gives an
additive functor. -/
theorem bifunctorMap_add_right {K K' : C₁} {L L' : C₂} (u : K ⟶ K') (v v' : L ⟶ L')
    [(T.obj K').Additive] :
    bifunctorMap T u (v + v') = bifunctorMap T u v + bifunctorMap T u v' := by
  dsimp only [bifunctorMap]
  rw [CategoryTheory.Functor.map_add, Preadditive.comp_add]

omit [Preadditive C₂] in
/-- **A bifunctor vanishes on a zero map in its first variable.** -/
theorem bifunctorMap_zero_left {K K' : C₁} {L L' : C₂} (v : L ⟶ L')
    [(T.flip.obj L).Additive] :
    bifunctorMap T (0 : K ⟶ K') v = 0 := by
  simpa using bifunctorMap_add_left T (0 : K ⟶ K') 0 v

omit [Preadditive C₁] in
/-- **A bifunctor vanishes on a zero map in its second variable.** -/
theorem bifunctorMap_zero_right {K K' : C₁} {L L' : C₂} (u : K ⟶ K')
    [(T.obj K').Additive] :
    bifunctorMap T u (0 : L ⟶ L') = 0 := by
  simpa using bifunctorMap_add_right T u (0 : L ⟶ L') 0

end BifunctorAdditive

/-! ### Functoriality of the derived external tensor product -/

section DerivedExternalTensor

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The map `u ⊠ v : K ⊠ L ⟶ K' ⊠ L'` of derived external tensor products induced by a map
`u : K ⟶ K'` on the first factor and a map `v : L ⟶ L'` on the second. -/
def derivedExternalTensorMap {K K' : DerivedCategory X.Modules}
    {L L' : DerivedCategory Y.Modules} (u : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensor f g K L ⟶ derivedExternalTensor f g K' L' :=
  bifunctorMap (Stacks.Duality.derivedTensor (pullback f g))
    ((Stacks.Duality.derivedPullback (pullback.fst f g)).map u)
    ((Stacks.Duality.derivedPullback (pullback.snd f g)).map v)

/-- **The derived external tensor product of a pair of identities is the identity.** -/
@[simp]
theorem derivedExternalTensorMap_id (K : DerivedCategory X.Modules)
    (L : DerivedCategory Y.Modules) :
    derivedExternalTensorMap f g (𝟙 K) (𝟙 L) = 𝟙 (derivedExternalTensor f g K L) := by
  have h := bifunctorMap_id (Stacks.Duality.derivedTensor (pullback f g))
    ((Stacks.Duality.derivedPullback (pullback.fst f g)).obj K)
    ((Stacks.Duality.derivedPullback (pullback.snd f g)).obj L)
  rwa [← CategoryTheory.Functor.map_id (Stacks.Duality.derivedPullback (pullback.fst f g)) K,
    ← CategoryTheory.Functor.map_id (Stacks.Duality.derivedPullback (pullback.snd f g)) L] at h

/-- **Derived external tensor products of maps compose factorwise.** -/
theorem derivedExternalTensorMap_comp {K K' K'' : DerivedCategory X.Modules}
    {L L' L'' : DerivedCategory Y.Modules} (u : K ⟶ K') (u' : K' ⟶ K'') (v : L ⟶ L')
    (v' : L' ⟶ L'') :
    derivedExternalTensorMap f g u v ≫ derivedExternalTensorMap f g u' v' =
      derivedExternalTensorMap f g (u ≫ u') (v ≫ v') := by
  have h := bifunctorMap_comp (Stacks.Duality.derivedTensor (pullback f g))
    ((Stacks.Duality.derivedPullback (pullback.fst f g)).map u)
    ((Stacks.Duality.derivedPullback (pullback.fst f g)).map u')
    ((Stacks.Duality.derivedPullback (pullback.snd f g)).map v)
    ((Stacks.Duality.derivedPullback (pullback.snd f g)).map v')
  rwa [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp] at h

/-- The defining factorization of `u ⊠ v` through `AlgebraicGeometry.bifunctorMap`. -/
theorem derivedExternalTensorMap_eq {K K' : DerivedCategory X.Modules}
    {L L' : DerivedCategory Y.Modules} (u : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensorMap f g u v
      = bifunctorMap (Stacks.Duality.derivedTensor (pullback f g))
          ((Stacks.Duality.derivedPullback (pullback.fst f g)).map u)
          ((Stacks.Duality.derivedPullback (pullback.snd f g)).map v) := rfl

/-- **The derived tensor product on a scheme is additive in its second variable.** -/
theorem additive_derivedTensor_obj (W : Scheme.{u}) (K : DerivedCategory W.Modules) :
    ((Stacks.Duality.derivedTensor W).obj K).Additive := by
  let : ((Stacks.Duality.derivedTensor W).obj K).CommShift ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor W.toRingedSpace).commShift_right K
  have : ((Stacks.Duality.derivedTensor W).obj K).IsTriangulated :=
    (Stacks.Cohomology.TorAmplitude.derTensor W.toRingedSpace).exact_right K
  infer_instance

/-- **The derived tensor product on a scheme is additive in its first variable.** -/
theorem additive_derivedTensor_flip_obj (W : Scheme.{u}) (L : DerivedCategory W.Modules) :
    ((Stacks.Duality.derivedTensor W).flip.obj L).Additive := by
  let : ((Stacks.Duality.derivedTensor W).flip.obj L).CommShift ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor W.toRingedSpace).commShift_left L
  have : ((Stacks.Duality.derivedTensor W).flip.obj L).IsTriangulated :=
    (Stacks.Cohomology.TorAmplitude.derTensor W.toRingedSpace).exact_left L
  infer_instance

/-- **The derived pullback along a morphism of schemes is additive.** -/
theorem additive_derivedPullback {Z W : Scheme.{u}} (h : Z ⟶ W) :
    (Stacks.Duality.derivedPullback h).Additive :=
  (Stacks.Duality.derivedAdjunction h).left_adjoint_additive

/-- **The derived external tensor product of maps is additive in its first variable.** -/
theorem derivedExternalTensorMap_add_left {K K' : DerivedCategory X.Modules}
    {L L' : DerivedCategory Y.Modules} (u u' : K ⟶ K') (v : L ⟶ L') :
    derivedExternalTensorMap f g (u + u') v
      = derivedExternalTensorMap f g u v + derivedExternalTensorMap f g u' v := by
  have := additive_derivedTensor_flip_obj (pullback f g)
    ((Stacks.Duality.derivedPullback (pullback.snd f g)).obj L)
  have := additive_derivedPullback (pullback.fst f g)
  simp only [derivedExternalTensorMap_eq, CategoryTheory.Functor.map_add]
  exact bifunctorMap_add_left _ _ _ _

/-- **The derived external tensor product of maps is additive in its second variable.** -/
theorem derivedExternalTensorMap_add_right {K K' : DerivedCategory X.Modules}
    {L L' : DerivedCategory Y.Modules} (u : K ⟶ K') (v v' : L ⟶ L') :
    derivedExternalTensorMap f g u (v + v')
      = derivedExternalTensorMap f g u v + derivedExternalTensorMap f g u v' := by
  have := additive_derivedTensor_obj (pullback f g)
    ((Stacks.Duality.derivedPullback (pullback.fst f g)).obj K')
  have := additive_derivedPullback (pullback.snd f g)
  simp only [derivedExternalTensorMap_eq, CategoryTheory.Functor.map_add]
  exact bifunctorMap_add_right _ _ _ _

/-- **The derived external tensor product of a zero map with any map is zero.** -/
theorem derivedExternalTensorMap_zero_left {K K' : DerivedCategory X.Modules}
    {L L' : DerivedCategory Y.Modules} (v : L ⟶ L') :
    derivedExternalTensorMap f g (0 : K ⟶ K') v = 0 := by
  simpa using derivedExternalTensorMap_add_left f g (0 : K ⟶ K') 0 v

/-- **The derived external tensor product of any map with a zero map is zero.** -/
theorem derivedExternalTensorMap_zero_right {K K' : DerivedCategory X.Modules}
    {L L' : DerivedCategory Y.Modules} (u : K ⟶ K') :
    derivedExternalTensorMap f g u (0 : L ⟶ L') = 0 := by
  simpa using derivedExternalTensorMap_add_right f g u (0 : L ⟶ L') 0

end DerivedExternalTensor

namespace DiagonalResolution

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}
  (R : DiagonalResolution f) (g : Y ⟶ Spec (.of A)) (F : perfectDerived X ⥤ perfectDerived Y)

/-! ### The second factors, and full faithfulness of `F` -/

/-- The `i`-th second factor `𝒢ᵢ` of a resolution of the diagonal as an object of
`D_perf(𝒪_X)`. -/
abbrev secondFactor (i : ℕ) : perfectDerived X :=
  ⟨(DerivedCategory.singleFunctor X.Modules 0).obj (R.right i),
    R.isPerfect_singleFunctor_right i⟩

/-! ### The pure maps on the two sides -/

/-- A map of second factors, read as a map of the corresponding objects of `D_perf(𝒪_X)`. -/
abbrev secondFactorHom {i j : ℕ} (b : R.right i ⟶ R.right j) :
    R.secondFactor i ⟶ R.secondFactor j :=
  ObjectProperty.homMk ((DerivedCategory.singleFunctor X.Modules 0).map b)

/-- The map of second factors attached to an identity is the identity. -/
@[simp]
theorem secondFactorHom_id (i : ℕ) :
    R.secondFactorHom (𝟙 (R.right i)) = 𝟙 (R.secondFactor i) := by
  apply ObjectProperty.hom_ext
  simp

/-- The map of second factors attached to a composite is the composite of the maps. -/
@[simp]
theorem secondFactorHom_comp {i j l : ℕ} (b : R.right i ⟶ R.right j)
    (b' : R.right j ⟶ R.right l) :
    R.secondFactorHom (b ≫ b') = R.secondFactorHom b ≫ R.secondFactorHom b' := by
  apply ObjectProperty.hom_ext
  simp

/-- The morphisms of `D_perf(𝒪_X)` between two objects are the morphisms of `D(𝒪_X)` between
the objects they sit over, the subcategory being full. -/
def perfectDerivedHomEquiv (P Q : perfectDerived X) : (P.obj ⟶ Q.obj) ≃ (P ⟶ Q) where
  toFun := ObjectProperty.homMk
  invFun h := h.hom
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Full faithfulness of `F` identifies `Hom(𝒢ᵢ, 𝒢ⱼ)` with `Hom(F(𝒢ᵢ), F(𝒢ⱼ))`**, a map of
second factors being read in degree zero of the derived category. -/
def secondFactorHomEquiv [F.Full] [F.Faithful] (i j : ℕ) :
    (R.right i ⟶ R.right j) ≃
      (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j)) :=
  ((Functor.FullyFaithful.ofFullyFaithful
        (DerivedCategory.singleFunctor X.Modules 0)).homEquiv (X := R.right i)
      (Y := R.right j)).trans
    ((perfectDerivedHomEquiv (R.secondFactor i) (R.secondFactor j)).trans
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv)

/-- `secondFactorHomEquiv` sends `b : 𝒢ᵢ ⟶ 𝒢ⱼ` to `F(b)`. -/
@[simp]
theorem secondFactorHomEquiv_apply [F.Full] [F.Faithful] {i j : ℕ}
    (b : R.right i ⟶ R.right j) :
    R.secondFactorHomEquiv F i j b = F.map (R.secondFactorHom b) :=
  rfl

/-- The pure map `a ⊠ F(b) : ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)` attached to a map `a : ℰᵢ ⟶ ℰⱼ` of first
factors and a map `b : 𝒢ᵢ ⟶ 𝒢ⱼ` of second factors. -/
def transformedMap {i j : ℕ} (a : R.left i ⟶ R.left j) (b : R.right i ⟶ R.right j) :
    R.imageTerm g F i ⟶ R.imageTerm g F j :=
  derivedExternalTensorMap f g ((DerivedCategory.singleFunctor X.Modules 0).map a)
    (F.map (R.secondFactorHom b)).hom

/-- **The pure transformed map of a pair of identities is the identity.** -/
theorem transformedMap_id (i : ℕ) :
    R.transformedMap g F (𝟙 (R.left i)) (𝟙 (R.right i)) = 𝟙 _ := by
  have hb : (F.map (R.secondFactorHom (𝟙 (R.right i)))).hom =
      𝟙 (F.obj (R.secondFactor i)).obj := by
    rw [R.secondFactorHom_id, CategoryTheory.Functor.map_id,
      ObjectProperty.FullSubcategory.id_hom]
  have h := derivedExternalTensorMap_id f g
    ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left i))
    (F.obj (R.secondFactor i)).obj
  rwa [← CategoryTheory.Functor.map_id (DerivedCategory.singleFunctor X.Modules 0) (R.left i),
    ← hb] at h

/-- **Pure transformed maps compose factorwise.** -/
theorem transformedMap_comp {i j l : ℕ} (a : R.left i ⟶ R.left j) (a' : R.left j ⟶ R.left l)
    (b : R.right i ⟶ R.right j) (b' : R.right j ⟶ R.right l) :
    R.transformedMap g F a b ≫ R.transformedMap g F a' b' =
      R.transformedMap g F (a ≫ a') (b ≫ b') := by
  have hb : (F.map (R.secondFactorHom (b ≫ b'))).hom =
      (F.map (R.secondFactorHom b)).hom ≫ (F.map (R.secondFactorHom b')).hom := by
    rw [R.secondFactorHom_comp, CategoryTheory.Functor.map_comp,
      ObjectProperty.FullSubcategory.comp_hom]
  have h := derivedExternalTensorMap_comp f g
    ((DerivedCategory.singleFunctor X.Modules 0).map a)
    ((DerivedCategory.singleFunctor X.Modules 0).map a')
    (F.map (R.secondFactorHom b)).hom (F.map (R.secondFactorHom b')).hom
  rwa [← CategoryTheory.Functor.map_comp, ← hb] at h

/-! ### The two pairings -/

/-- A pair of a map of first factors and a map of second factors, from index `i` to index `j`:
the data a pure map on either side is attached to. -/
abbrev FactorPair (i j : ℕ) : Type u :=
  (R.left i ⟶ R.left j) × (R.right i ⟶ R.right j)

/-- The convolution of formal combinations of pairs of maps of factors: pairs are composed
factorwise, and the pairing is extended additively in each variable. -/
def convolve {i j l : ℕ} (u : FreeAbelianGroup (R.FactorPair i j))
    (v : FreeAbelianGroup (R.FactorPair j l)) : FreeAbelianGroup (R.FactorPair i l) :=
  FreeAbelianGroup.lift
    (fun p ↦ FreeAbelianGroup.lift (fun q ↦ FreeAbelianGroup.of (p.1 ≫ q.1, p.2 ≫ q.2)) v) u

/-- **The additive extension of `(a, b) ↦ a ⊠ b`**, from formal integral combinations of pairs
of maps of factors to maps `ℰᵢ ⊠ 𝒢ᵢ ⟶ ℰⱼ ⊠ 𝒢ⱼ` on `X ×_A X`. -/
def boxPairing (i j : ℕ) :
    FreeAbelianGroup (R.FactorPair i j) →+ (R.boxTerm i ⟶ R.boxTerm j) :=
  FreeAbelianGroup.lift fun p ↦ externalTensorProductMap f f p.1 p.2

/-- **The additive extension of `(a, b) ↦ a ⊠ F(b)`**, from formal integral combinations of
pairs of maps of factors to maps `ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)` on `X ×_A Y`. -/
def transformedPairing (i j : ℕ) :
    FreeAbelianGroup (R.FactorPair i j) →+
      (R.imageTerm g F i ⟶ R.imageTerm g F j) :=
  FreeAbelianGroup.lift fun p ↦ R.transformedMap g F p.1 p.2

/-- The box pairing sends the generator of a pair `(a, b)` to `a ⊠ b`. -/
@[simp]
theorem boxPairing_of {i j : ℕ} (p : R.FactorPair i j) :
    R.boxPairing i j (FreeAbelianGroup.of p) = externalTensorProductMap f f p.1 p.2 :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The transformed pairing sends the generator of a pair `(a, b)` to `a ⊠ F(b)`. -/
@[simp]
theorem transformedPairing_of {i j : ℕ} (p : R.FactorPair i j) :
    R.transformedPairing g F i j (FreeAbelianGroup.of p) =
      R.transformedMap g F p.1 p.2 :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The box pairing carries a convolution to a composite.** -/
theorem boxPairing_convolve {i j l : ℕ} (u : FreeAbelianGroup (R.FactorPair i j))
    (v : FreeAbelianGroup (R.FactorPair j l)) :
    R.boxPairing i l (R.convolve u v) = R.boxPairing i j u ≫ R.boxPairing j l v :=
  freeAbelianGroup_lift_comp
    (fun p : R.FactorPair i j ↦ externalTensorProductMap f f p.1 p.2)
    (fun q : R.FactorPair j l ↦ externalTensorProductMap f f q.1 q.2)
    (fun r : R.FactorPair i l ↦ externalTensorProductMap f f r.1 r.2)
    (fun p q ↦ (p.1 ≫ q.1, p.2 ≫ q.2))
    (fun p q ↦ (externalTensorProductMap_comp f f p.1 q.1 p.2 q.2).symm) u v

/-- **The transformed pairing carries a convolution to a composite.** -/
theorem transformedPairing_convolve {i j l : ℕ} (u : FreeAbelianGroup (R.FactorPair i j))
    (v : FreeAbelianGroup (R.FactorPair j l)) :
    R.transformedPairing g F i l (R.convolve u v) =
      R.transformedPairing g F i j u ≫ R.transformedPairing g F j l v :=
  freeAbelianGroup_lift_comp
    (fun p : R.FactorPair i j ↦ R.transformedMap g F p.1 p.2)
    (fun q : R.FactorPair j l ↦ R.transformedMap g F q.1 q.2)
    (fun r : R.FactorPair i l ↦ R.transformedMap g F r.1 r.2)
    (fun p q ↦ (p.1 ≫ q.1, p.2 ≫ q.2))
    (fun p q ↦ (R.transformedMap_comp g F p.1 q.1 p.2 q.2).symm) u v

/-! ### The pairing on `X ×_A Y` through the images of the second factors -/

/-- A pair of a map of first factors and a map between the images under `F` of the second
factors. -/
abbrev ImagePair (i j : ℕ) : Type u :=
  (R.left i ⟶ R.left j) × (F.obj (R.secondFactor i) ⟶ F.obj (R.secondFactor j))

/-- **The additive extension of `(a, c) ↦ a ⊠ c`**, from formal integral combinations of pairs
of a map of first factors and a map of the images of the second factors to maps
`ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)` on `X ×_A Y`. -/
def transformedImagePairing (i j : ℕ) :
    FreeAbelianGroup (R.ImagePair F i j) →+
      (R.imageTerm g F i ⟶ R.imageTerm g F j) :=
  FreeAbelianGroup.lift fun p ↦
    derivedExternalTensorMap f g ((DerivedCategory.singleFunctor X.Modules 0).map p.1) p.2.hom

/-- The transformed image pairing sends the generator of a pair `(a, c)` to `a ⊠ c`. -/
@[simp]
theorem transformedImagePairing_of {i j : ℕ} (p : R.ImagePair F i j) :
    R.transformedImagePairing g F i j (FreeAbelianGroup.of p) =
      derivedExternalTensorMap f g ((DerivedCategory.singleFunctor X.Modules 0).map p.1)
        p.2.hom :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **For `F` fully faithful, if the maps `a ⊠ c` exhaust `Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))`, then
so do the pure maps `a ⊠ F(b)`**: surjectivity of the transformed image pairing gives
surjectivity of the transformed pairing. -/
theorem surjective_transformedPairing [F.Full] [F.Faithful]
    (h : ∀ i j, Function.Surjective (R.transformedImagePairing g F i j)) (i j : ℕ) :
    Function.Surjective (R.transformedPairing g F i j) := by
  intro φ
  obtain ⟨w, rfl⟩ := h i j φ
  refine ⟨FreeAbelianGroup.lift (fun p : R.ImagePair F i j ↦
    FreeAbelianGroup.of ((p.1, (R.secondFactorHomEquiv F i j).symm p.2) :
      R.FactorPair i j)) w, ?_⟩
  induction w using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p =>
    rw [FreeAbelianGroup.lift_apply_of, R.transformedPairing_of g F,
      R.transformedImagePairing_of g F, transformedMap,
      ← R.secondFactorHomEquiv_apply F, Equiv.apply_symm_apply]
  | neg p hp => rw [map_neg, map_neg, map_neg, hp]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-! ### The Künneth input, and the transport it determines -/

/-- **The Künneth identification of the Hom groups of the two families of terms, as data on the
two pairings.** Both pairings are surjective — every map between the terms on either side is a
sum of pure ones — and they have the same kernel, so that a formal combination of pairs of maps
of factors vanishes on one side exactly when it vanishes on the other. -/
structure KunnethHomData where
  /-- Künneth on `X ×_A X`: every map `ℰᵢ ⊠ 𝒢ᵢ ⟶ ℰⱼ ⊠ 𝒢ⱼ` is a sum of pure maps `a ⊠ b`. -/
  surjective_boxPairing (i j : ℕ) : Function.Surjective (R.boxPairing i j)
  /-- Künneth on `X ×_A Y`: every map `ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)` is a sum of pure maps
  `a ⊠ F(b)`. -/
  surjective_transformedPairing (i j : ℕ) :
    Function.Surjective (R.transformedPairing g F i j)
  /-- The two pairings have the same kernel. -/
  ker_eq (i j : ℕ) :
    (R.boxPairing i j).ker = (R.transformedPairing g F i j).ker

/-- **Künneth data from the two spanning statements.** For `F` fully faithful, if the pure maps
`a ⊠ b` exhaust `Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)`, the maps `a ⊠ c`, with `c` a map of the images of the
second factors, exhaust `Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))`, and the box and transformed pairings
have the same kernel, then these form Künneth data. -/
theorem KunnethHomData.of [F.Full] [F.Faithful]
    (hbox : ∀ i j, Function.Surjective (R.boxPairing i j))
    (himage : ∀ i j, Function.Surjective (R.transformedImagePairing g F i j))
    (hker : ∀ i j, (R.boxPairing i j).ker = (R.transformedPairing g F i j).ker) :
    KunnethHomData R g F where
  surjective_boxPairing := hbox
  surjective_transformedPairing := R.surjective_transformedPairing g F himage
  ker_eq := hker

namespace KunnethHomData

variable {R g F} (K : KunnethHomData R g F)

/-- **The Künneth identification of Hom groups.** It is the composite of the isomorphism of
`Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)` with the quotient of the formal combinations of pairs by the kernel of
the box pairing, the identification of that quotient with the quotient by the kernel of the
transformed pairing, and the isomorphism of the latter with
`Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))`. -/
def homEquiv (i j : ℕ) :
    (R.boxTerm i ⟶ R.boxTerm j) ≃+
      (R.imageTerm g F i ⟶ R.imageTerm g F j) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _ (K.surjective_boxPairing i j)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (K.ker_eq i j)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _
        (K.surjective_transformedPairing i j)))

/-- **The Künneth identification is the one the two pairings determine**: it carries the value
of the box pairing at a formal combination of pairs of maps of factors to the value of the
transformed pairing at the same combination. -/
theorem homEquiv_boxPairing (i j : ℕ) (u : FreeAbelianGroup (R.FactorPair i j)) :
    K.homEquiv i j (R.boxPairing i j u) = R.transformedPairing g F i j u := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (K.surjective_boxPairing i j)).symm (R.boxPairing i j u) =
      (QuotientAddGroup.mk u : _ ⧸ (R.boxPairing i j).ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  rw [homEquiv, AddEquiv.trans_apply, h]
  rfl

/-- **The Künneth identification carries a pure map to a pure map**: the transport of
`a ⊠ b : ℰᵢ ⊠ 𝒢ᵢ ⟶ ℰⱼ ⊠ 𝒢ⱼ` is `a ⊠ F(b) : ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)`. -/
theorem homEquiv_boxMap {i j : ℕ} (a : R.left i ⟶ R.left j) (b : R.right i ⟶ R.right j) :
    K.homEquiv i j (externalTensorProductMap f f a b) = R.transformedMap g F a b := by
  have := K.homEquiv_boxPairing i j (FreeAbelianGroup.of (a, b))
  rwa [R.boxPairing_of (a, b), R.transformedPairing_of g F (a, b)] at this

/-- **The transport of Hom groups determined by the Künneth identification**, whose additive
bijection is `AlgebraicGeometry.DiagonalResolution.KunnethHomData.homEquiv`. -/
def homTransport : ImageHomTransport R g F where
  hom := K.homEquiv
  hom_id i := by
    rw [← externalTensorProductMap_id f f (R.left i) (R.right i), K.homEquiv_boxMap,
      R.transformedMap_id]
  hom_comp i j l a b := by
    obtain ⟨u, rfl⟩ := K.surjective_boxPairing i j a
    obtain ⟨w, rfl⟩ := K.surjective_boxPairing j l b
    rw [← R.boxPairing_convolve, K.homEquiv_boxPairing, K.homEquiv_boxPairing,
      K.homEquiv_boxPairing, R.transformedPairing_convolve]

/-- **The differentials of the complex of [Stacks, Tag 0G0A] built from the Künneth
transport**: the differential from index `i + 1` to index `i` is the pure-map transport of the
differential `ℰᵢ₊₁ ⊠ 𝒢ᵢ₊₁ ⟶ ℰᵢ ⊠ 𝒢ᵢ` of the resolution of the diagonal. -/
theorem homTransport_complex_d (i : ℕ) :
    K.homTransport.complex.d (i + 1) i = K.homEquiv (i + 1) i (R.boxDifferential i) :=
  HomTransport.complex_d _ i

end KunnethHomData

/-! ### The complex of [Stacks, Tag 0G0A] -/

section KunnethComplex

variable [F.Full] [F.Faithful]
  (hbox : ∀ i j, Function.Surjective (R.boxPairing i j))
  (himage : ∀ i j, Function.Surjective (R.transformedImagePairing g F i j))
  (hker : ∀ i j, (R.boxPairing i j).ker = (R.transformedPairing g F i j).ker)

/-- **The identification of Hom groups behind the complex of [Stacks, Tag 0G0A]**, determined
by the Künneth decompositions `hbox` of `Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)` on `X ×_A X` and `himage` of
`Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))` on `X ×_A Y`, the equality `hker` of the kernels of the two
pairings, and the full faithfulness of `F`. -/
def kunnethHomEquiv (i j : ℕ) :
    (R.boxTerm i ⟶ R.boxTerm j) ≃+
      (R.imageTerm g F i ⟶ R.imageTerm g F j) :=
  (KunnethHomData.of R g F hbox himage hker).homEquiv i j

/-- **The identification is the Künneth one**: it carries the pure map
`a ⊠ b : ℰᵢ ⊠ 𝒢ᵢ ⟶ ℰⱼ ⊠ 𝒢ⱼ` to the pure map `a ⊠ F(b) : ℰᵢ ⊠ F(𝒢ᵢ) ⟶ ℰⱼ ⊠ F(𝒢ⱼ)`. -/
theorem kunnethHomEquiv_boxMap {i j : ℕ} (a : R.left i ⟶ R.left j)
    (b : R.right i ⟶ R.right j) :
    R.kunnethHomEquiv g F hbox himage hker i j (externalTensorProductMap f f a b) =
      R.transformedMap g F a b :=
  (KunnethHomData.of R g F hbox himage hker).homEquiv_boxMap a b

/-- The complex `… → ℰ₂ ⊠ F(𝒢₂) → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)` on `X ×_A Y` obtained from a
resolution of the diagonal of `X` by transforming its second factors by `F`: the complex of
[Stacks, Tag 0G0A], whose differentials are those of the resolution read through
`AlgebraicGeometry.DiagonalResolution.kunnethHomEquiv`.

Here `hbox` says that the pure maps `a ⊠ b` span `Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)`, `himage` that the maps
`a ⊠ c` with `c : F(𝒢ᵢ) ⟶ F(𝒢ⱼ)` span `Hom(ℰᵢ ⊠ F(𝒢ᵢ), ℰⱼ ⊠ F(𝒢ⱼ))`, and `hker` that a formal
combination of pairs of maps of factors vanishes on one side exactly when it vanishes on the
other. -/
def kunnethComplex : ChainComplex (DerivedCategory (pullback f g).Modules) ℕ :=
  (KunnethHomData.of R g F hbox himage hker).homTransport.complex

/-- The term of index `i` of the complex of [Stacks, Tag 0G0A] is `ℰᵢ ⊠ F(𝒢ᵢ)`. -/
@[simp]
theorem kunnethComplex_X (i : ℕ) :
    (R.kunnethComplex g F hbox himage hker).X i = R.imageTerm g F i :=
  rfl

/-- The differential of the complex from index `i + 1` to index `i` is the differential
`ℰᵢ₊₁ ⊠ 𝒢ᵢ₊₁ ⟶ ℰᵢ ⊠ 𝒢ᵢ` of the resolution of the diagonal, read through the identification of
Hom groups that the Künneth decompositions and the full faithfulness of `F` determine. -/
theorem kunnethComplex_d (i : ℕ) :
    (R.kunnethComplex g F hbox himage hker).d (i + 1) i =
      R.kunnethHomEquiv g F hbox himage hker (i + 1) i (R.boxDifferential i) :=
  (KunnethHomData.of R g F hbox himage hker).homTransport_complex_d i

end KunnethComplex

end DiagonalResolution

end AlgebraicGeometry

end
