module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.ModuleEquivalences
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineReconstruction
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# Rigidity of the reconstruction pair

Tag 0GP0 (`ModuleCat.exists_ringEquiv_invertible_iso_extensionTensorFunctor`) writes an
equivalence `F : ModuleCat A ⥤ ModuleCat B` of categories of modules over commutative rings as
extension of scalars along a ring isomorphism `e : A ≃+* B` followed by tensoring with an
invertible `B`-module `L`.  This file shows that the *ring isomorphism* in that description is
unique: the module `L` is not pinned down by `F` (it can be replaced by any module isomorphic
to it, and the comparison isomorphism is not unique either), but `e` is.  The same then holds
for the morphism of affine schemes in the conclusion of Tag 0GPJ.

The mechanism is the centre of the category.  `ModuleCat.ringEquivOfEquivalence` is the
canonical ring isomorphism attached to an equivalence, obtained from the induced isomorphism of
centres; `ModuleCat.map_regular_scalar` says that it transports the central scalars along `F`,
and that property determines it (`ModuleCat.ringEquivOfEquivalence_eq_of_map_smul_id`).  Since
the central scalars are natural transformations of the identity functor, conjugating by `F` is
insensitive to replacing `F` by a naturally isomorphic functor, so
`ModuleCat.ringEquivOfEquivalence` only depends on the isomorphism class of `F`
(`ModuleCat.ringEquivOfEquivalence_congr`).  Computing it on an
`ModuleCat.extensionTensorFunctor` returns the ring isomorphism one started from
(`ModuleCat.ringEquivOfEquivalence_extensionTensorFunctor`), and the two statements together
give the rigidity (`ModuleCat.eq_of_iso_extensionTensorFunctor`).

## Main results

* `ModuleCat.ringEquivOfEquivalence_eq_of_map_smul_id`: an additive equivalence
  `F : ModuleCat A ⥤ ModuleCat B` that carries `a • 𝟙 X` to `e a • 𝟙 (F.obj X)` has
  `ModuleCat.ringEquivOfEquivalence A B F = e`.  This is the uniqueness companion of
  `ModuleCat.map_regular_scalar`.
* `ModuleCat.ringEquivOfEquivalence_congr`: `ModuleCat.ringEquivOfEquivalence` depends on the
  equivalence only through its isomorphism class as a functor.
* `ModuleCat.ringEquivOfEquivalence_extensionTensorFunctor`:
  `ModuleCat.ringEquivOfEquivalence` inverts `ModuleCat.extensionTensorFunctor`, for any
  invertible module in the second slot.
* `ModuleCat.eq_of_iso_extensionTensorFunctor`: **affine rigidity at the ring level.**  If
  `extensionTensorFunctor A B φ L ≅ extensionTensorFunctor A B ψ M` with `L` and `M`
  invertible, then `φ = ψ`.
* `ModuleCat.eq_of_iso_extendScalars_comp_tensorRight`: the same for ring *homomorphisms*
  `φ ψ : A →+* B`, where neither functor need be an equivalence.  This is the form that a
  scheme-level rigidity statement needs, since two morphisms of affine schemes are not
  isomorphisms.
* `ModuleCat.isEquivalence_extensionTensorFunctor`: `ModuleCat.extensionTensorFunctor A B e L`
  is an equivalence when `L` is invertible.
* `AlgebraicGeometry.eq_of_iso_quasicoherentPullbackAffineTensor`: **affine rigidity at the
  scheme level.**  For `W` and `X` affine and `g g' : W ⟶ X`, if inverse image of
  quasi-coherent modules along `g` followed by tensoring with a `Γ(W, ⊤)`-module `L` is
  isomorphic to the same for `g'` and an invertible `M`, then `g = g'`.
* `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor`: the same with the hypothesis read at the
  level of sheaves of modules, through `AlgebraicGeometry.pullbackTensorFunctor`.

## Main definitions

* `AlgebraicGeometry.pullbackCompAffineQuasicoherentEquivOfHom` and
  `AlgebraicGeometry.extendScalarsCompAffineQuasicoherentEquivOfHom`: inverse image along an
  arbitrary morphism of affine schemes is extension of scalars on global sections.

## Implementation notes

The invertible module is deliberately *not* identified: the two hypotheses `L` and `M` of
`ModuleCat.eq_of_iso_extensionTensorFunctor` are unrelated, and only the ring map is asserted
to be rigid.  (It cannot be otherwise: tensoring with `L` and with any `L'` isomorphic to `L`
give isomorphic functors.)

Invertibility enters only to make `ModuleCat.extensionTensorFunctor A B e L` an equivalence,
which is what `ModuleCat.ringEquivOfEquivalence` needs as input.  It is obtained by combining
the equivalence `ModuleCat.extendScalars` of a ring isomorphism with
`CategoryTheory.MonoidalCategory.HasInverse.tensorRightEquivalence`, the two-sided tensor
inverse of `L` being its `Module.Dual`.

The scheme-level section only has to transport the ring-level statement.  Morphisms into an
affine scheme are determined by their action on global sections
(`AlgebraicGeometry.ext_of_isAffine`), and
`AlgebraicGeometry.extendScalarsCompAffineQuasicoherentEquivOfHom` turns inverse image along
`g` into extension of scalars along `g.appTop`; that comparison is
`AlgebraicGeometry.pullbackCompAffineQuasicoherentEquiv` with
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality` in place of the comparison of `g` with the
induced morphism of spectra, which was the only step of that chain special to an isomorphism.

The isomorphisms of functors in this file are cancelled with
`CategoryTheory.Iso.cancel_iso_hom_left` rather than `CategoryTheory.cancel_epi`: searching for
the `Epi` instance on a component of a natural isomorphism of functors between categories of
modules gets stuck on a universe constraint coming from the limit instances that the imports of
the scheme-level section bring into scope.
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

/-! ### The centre of `ModuleCat R`, read on morphisms -/

/-- The central scalar attached to `a : R` by `ModuleCat.centerRingEquiv` acts on an object `X`
of `ModuleCat R` as `a • 𝟙 X`. -/
theorem centerRingEquiv_app (R : Type u) [CommRing R] (a : R) (X : ModuleCat.{u} R) :
    (centerRingEquiv R a).app X = a • 𝟙 X := by
  show (CategoryTheory.Linear.toCatCenter R (ModuleCat.{u} R) a).app X = _
  simp [CategoryTheory.Linear.toCatCenter_apply_app]

/-! ### Uniqueness of the canonical ring isomorphism -/

/-- **`ModuleCat.ringEquivOfEquivalence` is the unique ring isomorphism transporting the central
scalars along `F`.**  This is the uniqueness companion of `ModuleCat.map_regular_scalar`: the
scalars `a • 𝟙 (-)` are natural in the object, so an equality `F.map (a • 𝟙 X) = e a • 𝟙 (F.obj
X)` holding for every `X` forces `e` to be the ring isomorphism that `F` induces on the centres
of the two categories. -/
theorem ringEquivOfEquivalence_eq_of_map_smul_id
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence] [F.Additive]
    (e : A ≃+* B)
    (h : ∀ (a : A) (X : ModuleCat.{u} A), F.map (a • 𝟙 X) = e a • 𝟙 (F.obj X)) :
    ringEquivOfEquivalence A B F = e := by
  refine RingEquiv.ext fun a => (centerRingEquiv B).injective ?_
  let W := MorphismProperty.isomorphisms (ModuleCat.{u} A)
  let : F.IsLocalization W := Functor.IsLocalization.of_isEquivalence F W le_rfl
  refine CatCenter.ext_of_localization F W _ _ fun X => ?_
  rw [← map_regular_scalar A B F a X, centerRingEquiv_app, h a X, centerRingEquiv_app]

/-! ### Invariance under natural isomorphism -/

/-- A natural isomorphism `F ≅ G` transports `F.map (a • 𝟙 X) = c • 𝟙` to the same for `G`. -/
private theorem map_smul_id_of_iso {A B : Type u} [CommRing A] [CommRing B]
    {F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B} (α : F ≅ G) (a : A) (X : ModuleCat.{u} A) (c : B)
    (h : F.map (a • 𝟙 X) = c • 𝟙 (F.obj X)) : G.map (a • 𝟙 X) = c • 𝟙 (G.obj X) := by
  refine ((α.app X).cancel_iso_hom_left _ _).mp ?_
  simp only [Iso.app_hom, Linear.comp_smul, Category.comp_id]
  rw [← α.hom.naturality, h, Linear.smul_comp, Category.id_comp]

/-- **The canonical ring isomorphism of an equivalence of module categories depends only on the
isomorphism class of the functor.**  If `F` and `G` are additive equivalences
`ModuleCat A ⥤ ModuleCat B` and `F ≅ G`, then
`ModuleCat.ringEquivOfEquivalence A B F = ModuleCat.ringEquivOfEquivalence A B G`.

The reason is that the centre of a category is built from natural endomorphisms of the identity
functor, and conjugating such an endomorphism by `F` or by `G` differs only by the natural
isomorphism `α`, which cancels. -/
theorem ringEquivOfEquivalence_congr
    (A B : Type u) [CommRing A] [CommRing B]
    (F G : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [F.IsEquivalence] [F.Additive] [G.IsEquivalence] [G.Additive]
    (α : F ≅ G) :
    ringEquivOfEquivalence A B F = ringEquivOfEquivalence A B G := by
  refine (ringEquivOfEquivalence_eq_of_map_smul_id A B G _ fun a X => ?_).symm
  refine map_smul_id_of_iso α a X _ ?_
  rw [← centerRingEquiv_app, map_regular_scalar A B F a X, centerRingEquiv_app]

/-! ### `ModuleCat.extensionTensorFunctor` is an equivalence -/

/-- An invertible module is a two-sided tensor inverse in `ModuleCat`, its inverse being its
dual. -/
noncomputable def hasInverse_of_invertible (B : Type u) [CommRing B] (L : ModuleCat.{u} B)
    [Module.Invertible B L] : HasInverse L where
  inv := ModuleCat.of B (Module.Dual B L)
  isoLeft := (TensorProduct.comm B L (Module.Dual B L) ≪≫ₗ
    Module.Invertible.linearEquiv B L).toModuleIso
  isoRight := (Module.Invertible.linearEquiv B L).toModuleIso

/-- Tensoring on the right with an invertible module is an equivalence of `ModuleCat B`. -/
theorem isEquivalence_tensorRight_of_invertible (B : Type u) [CommRing B] (L : ModuleCat.{u} B)
    [Module.Invertible B L] : (tensorRight L).IsEquivalence :=
  (hasInverse_of_invertible B L).tensorRightEquivalence.isEquivalence_functor

/-- **`ModuleCat.extensionTensorFunctor A B e L` is an equivalence when `L` is invertible**:
extension of scalars along a ring isomorphism is an equivalence, and so is tensoring with an
invertible module. -/
theorem isEquivalence_extensionTensorFunctor
    (A B : Type u) [CommRing A] [CommRing B] (e : A ≃+* B) (L : ModuleCat.{u} B)
    [Module.Invertible B L] : (extensionTensorFunctor A B e L).IsEquivalence :=
  have _h1 : (ModuleCat.restrictScalars e.toRingHom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  have h2 : (ModuleCat.extendScalars e.toRingHom).IsEquivalence :=
    (ModuleCat.extendRestrictScalarsAdj
      e.toRingHom).isEquivalence_left_of_isEquivalence_right
  have h3 : (tensorRight L).IsEquivalence := isEquivalence_tensorRight_of_invertible B L
  @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ h2 h3

/-! ### `ModuleCat.ringEquivOfEquivalence` inverts `ModuleCat.extensionTensorFunctor` -/

/-- Extension of scalars along `φ` carries the central scalar `a • 𝟙 M` to `φ a • 𝟙`. -/
theorem extendScalars_map_central_smul (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
    (M : ModuleCat.{u} A) (a : A) :
    (ModuleCat.extendScalars φ).map (a • 𝟙 M) =
      φ a • 𝟙 ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  show (1 : B) ⊗ₜ[A] (a • m) = φ a • ((1 : B) ⊗ₜ[A] m)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

/-- Tensoring on the right with `L` carries the central scalar `c • 𝟙 Y` to `c • 𝟙 (Y ⊗ L)`. -/
theorem tensorRight_map_smul_id (B : Type u) [CommRing B] (L Y : ModuleCat.{u} B) (c : B) :
    (tensorRight L).map (c • 𝟙 Y) = c • 𝟙 ((tensorRight L).obj Y) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro y l
  show ((c • 𝟙 Y) ▷ L).hom (y ⊗ₜ l) = _
  simp

/-- Extension of scalars along `φ` followed by tensoring with `L` carries the central scalar
`a • 𝟙 X` to `φ a • 𝟙`. -/
theorem extendScalars_comp_tensorRight_map_smul_id
    (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B) (L : ModuleCat.{u} B)
    (a : A) (X : ModuleCat.{u} A) :
    (ModuleCat.extendScalars φ ⋙ tensorRight L).map (a • 𝟙 X) =
      φ a • 𝟙 ((ModuleCat.extendScalars φ ⋙ tensorRight L).obj X) := by
  show (tensorRight L).map ((ModuleCat.extendScalars φ).map (a • 𝟙 X)) = _
  rw [extendScalars_map_central_smul, tensorRight_map_smul_id]
  rfl

/-- `ModuleCat.extensionTensorFunctor A B e L` carries the central scalar `a • 𝟙 X` to
`e a • 𝟙`. -/
theorem extensionTensorFunctor_map_smul_id
    (A B : Type u) [CommRing A] [CommRing B] (e : A ≃+* B) (L : ModuleCat.{u} B)
    (a : A) (X : ModuleCat.{u} A) :
    (extensionTensorFunctor A B e L).map (a • 𝟙 X) =
      e a • 𝟙 ((extensionTensorFunctor A B e L).obj X) :=
  extendScalars_comp_tensorRight_map_smul_id A B e.toRingHom L a X

/-- **`ModuleCat.ringEquivOfEquivalence` inverts `ModuleCat.extensionTensorFunctor`.**  The
canonical ring isomorphism attached to extension of scalars along `e` followed by tensoring
with an invertible module is `e` itself; the module plays no role. -/
theorem ringEquivOfEquivalence_extensionTensorFunctor
    (A B : Type u) [CommRing A] [CommRing B] (e : A ≃+* B) (L : ModuleCat.{u} B)
    [Module.Invertible B L] :
    let : (extensionTensorFunctor A B e L).IsEquivalence :=
      isEquivalence_extensionTensorFunctor A B e L
    let : (extensionTensorFunctor A B e L).Additive :=
      Functor.additive_of_preserves_binary_products _
    ringEquivOfEquivalence A B (extensionTensorFunctor A B e L) = e := by
  intro _ _
  exact ringEquivOfEquivalence_eq_of_map_smul_id A B _ e
    (extensionTensorFunctor_map_smul_id A B e L)

/-! ### Affine rigidity at the ring level -/

/-- **Affine rigidity of the reconstruction pair, at the ring level.**  If extension of scalars
along `φ` followed by tensoring with an invertible module `L` is isomorphic, as a functor
`ModuleCat A ⥤ ModuleCat B`, to extension of scalars along `ψ` followed by tensoring with an
invertible module `M`, then `φ = ψ`.

Only the ring isomorphism is rigid: nothing is claimed about `L` and `M`, and nothing can be,
since isomorphic modules give isomorphic tensoring functors. -/
theorem eq_of_iso_extensionTensorFunctor
    (A B : Type u) [CommRing A] [CommRing B] (φ ψ : A ≃+* B) (L M : ModuleCat.{u} B)
    [Module.Invertible B L] [Module.Invertible B M]
    (i : extensionTensorFunctor A B φ L ≅ extensionTensorFunctor A B ψ M) :
    φ = ψ := by
  have h : ∀ (e : A ≃+* B) (N : ModuleCat.{u} B) [Module.Invertible B N],
      (extensionTensorFunctor A B e N).IsEquivalence ∧ (extensionTensorFunctor A B e N).Additive :=
    fun e N _ => have := isEquivalence_extensionTensorFunctor A B e N
      ⟨this, Functor.additive_of_preserves_binary_products _⟩
  obtain ⟨_, _⟩ := h φ L
  obtain ⟨_, _⟩ := h ψ M
  calc φ = ringEquivOfEquivalence A B (extensionTensorFunctor A B φ L) :=
        (ringEquivOfEquivalence_extensionTensorFunctor A B φ L).symm
    _ = ringEquivOfEquivalence A B (extensionTensorFunctor A B ψ M) :=
        ringEquivOfEquivalence_congr A B _ _ i
    _ = ψ := ringEquivOfEquivalence_extensionTensorFunctor A B ψ M

/-- **Affine rigidity for ring homomorphisms.**  The same conclusion as
`ModuleCat.eq_of_iso_extensionTensorFunctor` with `φ` and `ψ` merely ring *homomorphisms*, so
that neither functor need be an equivalence.  Only the module in the second slot has to be
invertible, and only to know that its scalars are faithful.

The centre of the category is unavailable here — a functor that is not an equivalence induces
no isomorphism of centres — so this is proved directly: naturality of the comparison
isomorphism at the central scalar `a • 𝟙 X`, cancelled against the comparison isomorphism,
gives `φ a • 𝟙 Y = ψ a • 𝟙 Y` at every `Y` in the image, and `X = A` makes `Y` the module
`M`.

This is the form in which the ring-level rigidity feeds the scheme-level statement, where the
two morphisms of affine schemes are not assumed to be isomorphisms. -/
theorem eq_of_iso_extendScalars_comp_tensorRight
    (A B : Type u) [CommRing A] [CommRing B] (φ ψ : A →+* B) (L M : ModuleCat.{u} B)
    [Module.Invertible B M]
    (i : ModuleCat.extendScalars φ ⋙ tensorRight L ≅
      ModuleCat.extendScalars ψ ⋙ tensorRight M) :
    φ = ψ := by
  ext a
  -- At every object the two central scalars agree, by naturality of `i` at `a • 𝟙 X`.
  have key : ∀ X : ModuleCat.{u} A,
      φ a • 𝟙 ((ModuleCat.extendScalars ψ ⋙ tensorRight M).obj X) =
        ψ a • 𝟙 ((ModuleCat.extendScalars ψ ⋙ tensorRight M).obj X) := fun X =>
    (map_smul_id_of_iso i a X _ (extendScalars_comp_tensorRight_map_smul_id ..)).symm.trans
      (extendScalars_comp_tensorRight_map_smul_id ..)
  -- At `X = A` the object is `M`, up to the unit comparison of extension of scalars.
  let d : M ≅ (ModuleCat.extendScalars ψ ⋙ tensorRight M).obj (ModuleCat.of A A) :=
    (λ_ M).symm ≪≫ (tensorRight M).mapIso
      (Functor.Monoidal.εIso (ModuleCat.extendScalars ψ))
  have hM : φ a • 𝟙 M = ψ a • 𝟙 M := by
    have h := congrArg (fun f => d.hom ≫ f ≫ d.inv) (key (ModuleCat.of A A))
    simpa only [Linear.comp_smul, Linear.smul_comp, Category.id_comp,
      Iso.hom_inv_id] using h
  refine FaithfulSMul.eq_of_smul_eq_smul (α := (M : Type u)) fun m => ?_
  simpa using congrArg (fun f => f.hom m) hM

end ModuleCat

namespace AlgebraicGeometry

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

variable {W X : Scheme.{u}} [IsAffine W] [IsAffine X]

/-! ### Pullback along a morphism of affine schemes is extension of scalars -/

open Stacks.Descent in
/-- **Inverse image along a morphism of affine schemes is extension of scalars on global
sections**, on modules rather than on quasi-coherent modules.  This is
`AlgebraicGeometry.pullbackCompAffineQuasicoherentEquiv` for an arbitrary morphism in place of
the isomorphism attached to a ring isomorphism: the only ingredient that was special to an
isomorphism was the comparison of `g` with the induced morphism of spectra, and for a general
`g` that is `AlgebraicGeometry.Scheme.isoSpec_hom_naturality`. -/
noncomputable def pullbackCompAffineQuasicoherentEquivOfHom (g : W ⟶ X) :
    ((affineQuasicoherentModulesEquiv X).functor ⋙
        ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)) ⋙
        Scheme.Modules.pullback g ≅
      ModuleCat.extendScalars g.appTop.hom ⋙
        (affineQuasicoherentModulesEquiv W).functor ⋙
          ObjectProperty.ι (SheafOfModules.isQuasicoherent W.ringCatSheaf) :=
  Functor.isoWhiskerRight (affineQuasicoherentModulesEquivCompι X)
      (Scheme.Modules.pullback g) ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, ⊤))
      (Scheme.Modules.pullbackComp g X.isoSpec.hom) ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, ⊤))
      (Scheme.Modules.pullbackCongr (Scheme.isoSpec_hom_naturality g).symm) ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, ⊤))
      (Scheme.Modules.pullbackComp W.isoSpec.hom (Spec.map g.appTop)).symm ≪≫
    Functor.isoWhiskerRight (extendScalarsCompTildeIso g.appTop).symm
      (Scheme.Modules.pullback W.isoSpec.hom) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars g.appTop.hom)
      (affineQuasicoherentModulesEquivCompι W).symm

/-- **Inverse image of quasi-coherent modules along a morphism of affine schemes is extension of
scalars on global sections.**  This is
`AlgebraicGeometry.pullbackCompAffineQuasicoherentEquivOfHom` with quasi-coherence restored, the
inclusion of the quasi-coherent modules being fully faithful. -/
noncomputable def extendScalarsCompAffineQuasicoherentEquivOfHom (g : W ⟶ X) :
    (affineQuasicoherentModulesEquiv X).functor ⋙ quasicoherentPullback g ≅
      ModuleCat.extendScalars g.appTop.hom ⋙ (affineQuasicoherentModulesEquiv W).functor :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.ringCatSheaf))
    (pullbackCompAffineQuasicoherentEquivOfHom g)

/-- Read through the affine comparison, `AlgebraicGeometry.affineTensorFunctor` is tensoring
with the module itself: the comparison cancels against its own unit. -/
noncomputable def affineQuasicoherentEquivCompAffineTensor (W : Scheme.{u}) [IsAffine W]
    (L : ModuleCat.{u} Γ(W, ⊤)) :
    (affineQuasicoherentModulesEquiv W).functor ⋙ affineTensorFunctor W L ≅
      tensorRight L ⋙ (affineQuasicoherentModulesEquiv W).functor :=
  Functor.isoWhiskerRight (affineQuasicoherentModulesEquiv W).unitIso.symm
      (tensorRight L ⋙ (affineQuasicoherentModulesEquiv W).functor) ≪≫
    Functor.leftUnitor _

/-! ### Affine rigidity at the scheme level -/

/-- **Affine rigidity of the reconstruction pair, at the scheme level.**  For `W` and `X` affine
schemes, two morphisms `g g' : W ⟶ X` and two `Γ(W, ⊤)`-modules `L` and `M` with `M`
invertible, if inverse image of quasi-coherent modules along `g` followed by tensoring with `L`
is isomorphic to inverse image along `g'` followed by tensoring with `M`, then `g = g'`.

Morphisms into an affine scheme are determined by their action on global sections
(`AlgebraicGeometry.ext_of_isAffine`), and on global sections the two composites become
extension of scalars followed by tensoring, where
`ModuleCat.eq_of_iso_extendScalars_comp_tensorRight` applies.  As at the ring level, the module
is not identified; only the morphism is rigid. -/
theorem eq_of_iso_quasicoherentPullbackAffineTensor (g g' : W ⟶ X)
    (L M : ModuleCat.{u} Γ(W, ⊤)) [Module.Invertible Γ(W, ⊤) M]
    (i : quasicoherentPullback g ⋙ affineTensorFunctor W L ≅
      quasicoherentPullback g' ⋙ affineTensorFunctor W M) :
    g = g' := by
  refine ext_of_isAffine (CommRingCat.hom_ext ?_)
  refine ModuleCat.eq_of_iso_extendScalars_comp_tensorRight Γ(X, ⊤) Γ(W, ⊤)
    g.appTop.hom g'.appTop.hom L M ?_
  refine Functor.fullyFaithfulCancelRight (affineQuasicoherentModulesEquiv W).functor ?_
  exact (Functor.isoWhiskerRight (extendScalarsCompAffineQuasicoherentEquivOfHom g)
        (affineTensorFunctor W L) ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars g.appTop.hom)
        (affineQuasicoherentEquivCompAffineTensor W L)).symm ≪≫
    Functor.isoWhiskerLeft (affineQuasicoherentModulesEquiv X).functor i ≪≫
    Functor.isoWhiskerRight (extendScalarsCompAffineQuasicoherentEquivOfHom g')
        (affineTensorFunctor W M) ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars g'.appTop.hom)
        (affineQuasicoherentEquivCompAffineTensor W M)

/-- **Affine rigidity of the reconstruction pair, at the level of sheaves of modules.**  The
same conclusion as `AlgebraicGeometry.eq_of_iso_quasicoherentPullbackAffineTensor` with the
hypothesis stated for `AlgebraicGeometry.pullbackTensorFunctor`, i.e. for inverse image
followed by the tensor product of sheaves of `𝒪_W`-modules, as functors into all
`𝒪_W`-modules.

The two invertible sheaves are presented as the inverse images along `W ≅ Spec Γ(W, ⊤)` of the
sheaves associated to `Γ(W, ⊤)`-modules, which is the form in which
`AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_quasicoherentEquivalence` produces
them. -/
theorem eq_of_iso_pullbackTensorFunctor (g g' : W ⟶ X)
    (L M : ModuleCat.{u} Γ(W, ⊤)) [Module.Invertible Γ(W, ⊤) M]
    (i : pullbackTensorFunctor g ((Stacks.RingedSpace.pullbackFunctor
          W.isoSpec.hom.toLRSHom.toShHom).obj (tilde L)) ≅
        pullbackTensorFunctor g' ((Stacks.RingedSpace.pullbackFunctor
          W.isoSpec.hom.toLRSHom.toShHom).obj (tilde M))) :
    g = g' := by
  refine eq_of_iso_quasicoherentPullbackAffineTensor g g' L M ?_
  refine Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent W.ringCatSheaf)) ?_
  exact Functor.isoWhiskerLeft (quasicoherentPullback g) (affineTensorFunctorCompι W L) ≪≫
    i ≪≫
    (Functor.isoWhiskerLeft (quasicoherentPullback g') (affineTensorFunctorCompι W M)).symm

end AlgebraicGeometry
