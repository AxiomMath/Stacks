module

public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceVectorBundle
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedSymmetricUniversal
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafDegreewise
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor of points of a vector bundle

Let `ℱ` be a quasi-coherent `𝒪_X`-module and `𝐕(ℱ) = Spec_X(Sym(ℱ))` its vector bundle. For a
scheme `h : W ⟶ X` over `X`, a morphism `W ⟶ 𝐕(ℱ)` over `X` is the same thing as a morphism of
`𝒪_X`-modules `ℱ ⟶ h_* 𝒪_W`: by the universal property of the relative spectrum it is a morphism
of `𝒪_X`-algebras `Sym(ℱ) ⟶ h_* 𝒪_W`, and by the universal property of the symmetric algebra
such a morphism is determined by its restriction to `ℱ`. The bijection is natural in `W`, and a
morphism `𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)` induced by `f : ℱ ⟶ 𝒢` acts on it by precomposition with `f`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.vectorBundleHomEquiv` — the bijection
  `Hom_X(W, 𝐕(ℱ)) ≃ Hom_{𝒪_X}(ℱ, h_* 𝒪_W)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.vectorBundleHomEquiv_comp` — naturality in `W`.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleHomEquiv_comp_vectorBundleMap` — naturality in
  `ℱ`.

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The module `h_* 𝒪_W` of a scheme `h : W ⟶ X` over `X`. -/
abbrev structurePushforward {W : Scheme.{u}} (h : W ⟶ X) : X.Modules :=
  (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)

variable (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]

/-- The comparison of the two ungraded realizations of the graded algebra `Sym(ℱ)`, with its
target spelled as the algebra sheaf `Sym(ℱ)` of `𝐕(ℱ)`. -/
def symmetricAlgebraSheafComparison :
    ungradedAlgebraSheaf X (symmetricAlgebra X F) (symmetricAlgebra_mul_comm X F) ≅
      symmetricAlgebraSheaf X F :=
  ungradedAlgebraSheafIsoGradedAlgebraSheaf X (symmetricAlgebra X F)
    (symmetricAlgebra_mul_comm X F)

/-- **The functor of points of the vector bundle `𝐕(ℱ)`**: a morphism `W ⟶ 𝐕(ℱ)` of schemes over
`X` is the same thing as a morphism of `𝒪_X`-modules `ℱ ⟶ h_* 𝒪_W`. -/
def vectorBundleHomEquiv (W : Over X) :
    (W ⟶ vectorBundleOver X (F := F)) ≃ (F ⟶ structurePushforward W.hom) :=
  haveI := isAffineHom_vectorBundleOver X (F := F)
  (overHomEquivAlgebraHom W (vectorBundleOver X (F := F))).trans <|
    ((vectorBundlePushforwardIso X (F := F)).homCongr (Iso.refl _)).trans <|
    ((symmetricAlgebraSheafComparison F).symm.homCongr (Iso.refl _)).trans <|
    ungradedAlgebraSheafModuleHomEquiv (symmetricAlgebra X F) (symmetricAlgebra_mul_comm X F)
      (pushforwardAlgebra W.hom) (symmetricAlgebraGen X F)
      (isSymmetricAlgebra_symmetricAlgebra X F)

/-- The bijection, written out: the module morphism attached to `u : W ⟶ 𝐕(ℱ)` is the restriction
to `ℱ` of the morphism of algebras `Sym(ℱ) ⟶ h_* 𝒪_W` that `u` induces on pushed-forward
structure sheaves. -/
theorem vectorBundleHomEquiv_apply (W : Over X) (u : W ⟶ vectorBundleOver X (F := F)) :
    haveI := isAffineHom_vectorBundleOver X (F := F)
    vectorBundleHomEquiv F W u =
      ungradedAlgebraSheafModuleHomEquiv (symmetricAlgebra X F) (symmetricAlgebra_mul_comm X F)
        (pushforwardAlgebra W.hom) (symmetricAlgebraGen X F)
        (isSymmetricAlgebra_symmetricAlgebra X F)
        ((symmetricAlgebraSheafComparison F).hom ≫
          (vectorBundlePushforwardIso X (F := F)).inv ≫ pushforwardAlgebraMap u) := by
  simp only [vectorBundleHomEquiv, Equiv.trans_apply, overHomEquivAlgebraHom_apply,
    Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rfl

/-- **The functor of points of `𝐕(ℱ)` is natural in the test scheme**: precomposing with
`a : W' ⟶ W` postcomposes the module morphism with the canonical map `h_* 𝒪_W ⟶ h'_* 𝒪_{W'}`. -/
theorem vectorBundleHomEquiv_comp {W W' : Over X} (a : W' ⟶ W)
    (u : W ⟶ vectorBundleOver X (F := F)) :
    vectorBundleHomEquiv F W' (a ≫ u) =
      vectorBundleHomEquiv F W u ≫ AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap a) := by
  have := isAffineHom_vectorBundleOver X (F := F)
  have h : (symmetricAlgebraSheafComparison F).hom ≫ (vectorBundlePushforwardIso X (F := F)).inv ≫
        pushforwardAlgebraMap (a ≫ u) =
      ((symmetricAlgebraSheafComparison F).hom ≫ (vectorBundlePushforwardIso X (F := F)).inv ≫
        pushforwardAlgebraMap u) ≫ pushforwardAlgebraMap a := by
    rw [pushforwardAlgebraMap_comp]
    simp only [Category.assoc]
  rw [vectorBundleHomEquiv_apply, vectorBundleHomEquiv_apply, h]
  exact ungradedAlgebraSheafModuleHomEquiv_comp (symmetricAlgebra X F)
    (symmetricAlgebra_mul_comm X F) (pushforwardAlgebra W.hom) (symmetricAlgebraGen X F)
    (isSymmetricAlgebra_symmetricAlgebra X F) (pushforwardAlgebra W'.hom) _
    (pushforwardAlgebraMap a)

variable {F} {G : SheafOfModules.{u} X.ringCatSheaf} [G.IsQuasicoherent]

omit [F.IsQuasicoherent] [G.IsQuasicoherent] in
/-- The module morphism attached to a morphism of algebras `Sym(ℱ) ⟶ 𝒜` that factors through
`Sym(f) : Sym(ℱ) ⟶ Sym(𝒢)` is `f` followed by the one attached to the second factor. -/
theorem ungradedAlgebraSheafModuleHomEquiv_symmetricAlgebraSheafMap (f : F ⟶ G)
    (𝒜 : AlgebraSheaf X) (ψ : symmetricAlgebraSheaf X G ⟶ 𝒜) :
    ungradedAlgebraSheafModuleHomEquiv (symmetricAlgebra X F) (symmetricAlgebra_mul_comm X F)
        𝒜 (symmetricAlgebraGen X F) (isSymmetricAlgebra_symmetricAlgebra X F)
        ((symmetricAlgebraSheafComparison F).hom ≫ symmetricAlgebraSheafMap X f ≫ ψ) =
      f ≫ ungradedAlgebraSheafModuleHomEquiv (symmetricAlgebra X G)
        (symmetricAlgebra_mul_comm X G) 𝒜 (symmetricAlgebraGen X G)
        (isSymmetricAlgebra_symmetricAlgebra X G)
        ((symmetricAlgebraSheafComparison G).hom ≫ ψ) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  obtain ⟨U⟩ := W
  change (ψ.right.hom.app (op U)).hom (((symmetricAlgebraSheafMap X f).right.hom.app (op U)).hom
      (((ungradedToGradedRight X (symmetricAlgebra X F) (symmetricAlgebra_mul_comm X F)).hom.app
        (op U)).hom (ungradedAlgebraSheafIncl X (symmetricAlgebra X F)
          (symmetricAlgebra_mul_comm X F) 1 U
          ((symmetricAlgebraGen X F).val.app (op U) s)))) =
    (ψ.right.hom.app (op U)).hom
      (((ungradedToGradedRight X (symmetricAlgebra X G) (symmetricAlgebra_mul_comm X G)).hom.app
        (op U)).hom (ungradedAlgebraSheafIncl X (symmetricAlgebra X G)
          (symmetricAlgebra_mul_comm X G) 1 U
          ((symmetricAlgebraGen X G).val.app (op U) (f.val.app (op U) s))))
  rw [ungradedToGradedRight_ungradedAlgebraSheafIncl,
    ungradedToGradedRight_ungradedAlgebraSheafIncl]
  refine congrArg (ψ.right.hom.app (op U)).hom ((symmetricAlgebraSheafMap_ungradedIncl X f (op U) 1
    _).trans (congrArg ((symmetricAlgebra X G).ungradedIncl 1) ?_))
  exact congrArg (fun φ : F ⟶ (symmetricAlgebra X G).piece 1 => φ.val.app (op U) s)
    (symmetricAlgebraGen_comp_symmetricAlgebraUnitalHom X f)

/-- **The functor of points of `𝐕` is natural in the module**: composing `u : W ⟶ 𝐕(𝒢)` with
`𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)` precomposes the module morphism attached to `u` with `f : ℱ ⟶ 𝒢`. -/
theorem vectorBundleHomEquiv_comp_vectorBundleMap (f : F ⟶ G) (W : Over X)
    (u : W ⟶ vectorBundleOver X (F := G)) :
    vectorBundleHomEquiv F W (u ≫ vectorBundleMap X f) = f ≫ vectorBundleHomEquiv G W u := by
  have := isAffineHom_vectorBundleOver X (F := F)
  have := isAffineHom_vectorBundleOver X (F := G)
  have h : (symmetricAlgebraSheafComparison F).hom ≫ (vectorBundlePushforwardIso X (F := F)).inv ≫
        pushforwardAlgebraMap (u ≫ vectorBundleMap X f) =
      (symmetricAlgebraSheafComparison F).hom ≫ symmetricAlgebraSheafMap X f ≫
        (vectorBundlePushforwardIso X (F := G)).inv ≫ pushforwardAlgebraMap u := by
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_vectorBundleMap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [vectorBundleHomEquiv_apply, vectorBundleHomEquiv_apply, h]
  exact ungradedAlgebraSheafModuleHomEquiv_symmetricAlgebraSheafMap f _ _

/-- Naturality of `vectorBundleHomEquiv` in the module, on a point given by a module morphism. -/
private theorem vectorBundleHomEquiv_symm_comp_vectorBundleMap (f : F ⟶ G) (W : Over X)
    (φ : G ⟶ structurePushforward W.hom) :
    vectorBundleHomEquiv F W ((vectorBundleHomEquiv G W).symm φ ≫ vectorBundleMap X f) = f ≫ φ := by
  rw [vectorBundleHomEquiv_comp_vectorBundleMap, Equiv.apply_symm_apply]

/-- Naturality of `vectorBundleHomEquiv` in the test scheme, on a point given by a module
morphism. -/
private theorem vectorBundleHomEquiv_comp_symm {W W' : Over X} (a : W' ⟶ W)
    (φ : F ⟶ structurePushforward W.hom) :
    vectorBundleHomEquiv F W' (a ≫ (vectorBundleHomEquiv F W).symm φ) =
      φ ≫ AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap a) := by
  rw [vectorBundleHomEquiv_comp, Equiv.apply_symm_apply]

/-! ### Base change -/

section BaseChange

variable {T : Scheme.{u}} (g : T ⟶ X) (F : X.Modules) [F.IsQuasicoherent]

/-- **Transposition along `g`**: a module morphism `g^*ℱ ⟶ h_* 𝒪_W` for a scheme `h : W ⟶ T` over
`T` is the same thing as a module morphism `ℱ ⟶ (h ≫ g)_* 𝒪_W`, by the adjunction `g^* ⊣ g_*`. -/
def transposeEquiv (W : Over T) :
    ((Scheme.Modules.pullback g).obj F ⟶ structurePushforward W.hom) ≃
      (F ⟶ structurePushforward ((Over.map g).obj W).hom) where
  toFun φ := (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F _ φ ≫
    ((Scheme.Modules.pushforwardComp W.hom g).app _).hom
  invFun ψ := ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F _).symm
    (ψ ≫ ((Scheme.Modules.pushforwardComp W.hom g).app _).inv)
  left_inv φ := by simp
  right_inv ψ := by simp

omit [SheafOfModules.IsQuasicoherent F] in
/-- Transposition, written out. -/
theorem transposeEquiv_apply (W : Over T)
    (φ : (Scheme.Modules.pullback g).obj F ⟶ structurePushforward W.hom) :
    transposeEquiv g F W φ =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv F _ φ ≫
        ((Scheme.Modules.pushforwardComp W.hom g).app _).hom := rfl

/-- The canonical maps on pushed-forward structure sheaves are compatible with pushing forward
along `g`. -/
theorem pushforward_map_underlyingModuleMap {W W' : Over T} (a : W' ⟶ W) :
    (Scheme.Modules.pushforward g).map
          (AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap a)) ≫
        ((Scheme.Modules.pushforwardComp W'.hom g).app
          (SheafOfModules.unit W'.left.ringCatSheaf)).hom =
      ((Scheme.Modules.pushforwardComp W.hom g).app
          (SheafOfModules.unit W.left.ringCatSheaf)).hom ≫
        AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap ((Over.map g).map a)) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  obtain ⟨U⟩ := U
  change ((pushforwardAlgebraMap a).right.hom.app (op (g ⁻¹ᵁ U))).hom x =
    ((pushforwardAlgebraMap ((Over.map g).map a)).right.hom.app (op U)).hom x
  rw [pushforwardAlgebraMap_app a (g ⁻¹ᵁ U) (Over.w a ▸ le_rfl),
    pushforwardAlgebraMap_app ((Over.map g).map a) U (Over.w ((Over.map g).map a) ▸ le_rfl)]
  rfl

omit [SheafOfModules.IsQuasicoherent F] in
/-- **Transposition is natural in the test scheme.** -/
theorem transposeEquiv_comp {W W' : Over T} (a : W' ⟶ W)
    (φ : (Scheme.Modules.pullback g).obj F ⟶ structurePushforward W.hom) :
    transposeEquiv g F W' (φ ≫ AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap a)) =
      transposeEquiv g F W φ ≫
        AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap ((Over.map g).map a)) := by
  rw [transposeEquiv_apply, transposeEquiv_apply]
  exact (congrArg (· ≫ ((Scheme.Modules.pushforwardComp W'.hom g).app _).hom)
      (Adjunction.homEquiv_naturality_right _ φ _)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (pushforward_map_underlyingModuleMap g a)).trans (Category.assoc _ _ _).symm))

variable [((Scheme.Modules.pullback g).obj F).IsQuasicoherent]

/-- **The base change of a vector bundle, on points**: a morphism `W ⟶ 𝐕(g^*ℱ)` over `T` is the
same thing as a morphism `W ⟶ 𝐕(ℱ) ×_X T` over `T`. -/
def baseChangeHomEquiv (W : Over T) :
    (W ⟶ vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F)) ≃
      (W ⟶ (Over.pullback g).obj (vectorBundleOver X (F := F))) :=
  (vectorBundleHomEquiv _ W).trans <| (transposeEquiv g F W).trans <|
    (vectorBundleHomEquiv F ((Over.map g).obj W)).symm.trans
      ((Over.mapPullbackAdj g).homEquiv _ _)

/-- The base-change bijection is natural in the test scheme. -/
theorem baseChangeHomEquiv_comp {W W' : Over T} (a : W' ⟶ W)
    (u : W ⟶ vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F)) :
    baseChangeHomEquiv g F W' (a ≫ u) = a ≫ baseChangeHomEquiv g F W u := by
  have h1 : (vectorBundleHomEquiv F ((Over.map g).obj W')).symm
        (transposeEquiv g F W' (vectorBundleHomEquiv _ W' (a ≫ u))) =
      (Over.map g).map a ≫ (vectorBundleHomEquiv F ((Over.map g).obj W)).symm
        (transposeEquiv g F W (vectorBundleHomEquiv _ W u)) :=
    (Equiv.symm_apply_eq _).2 <|
      ((congrArg (transposeEquiv g F W') (vectorBundleHomEquiv_comp _ a u)).trans
        (transposeEquiv_comp g F a _)).trans
        (vectorBundleHomEquiv_comp_symm ((Over.map g).map a) _).symm
  exact (congrArg ((Over.mapPullbackAdj g).homEquiv W' _) h1).trans
    ((Over.mapPullbackAdj g).homEquiv_naturality_left _ _)

/-- **The vector bundle of a pullback is the pullback of the vector bundle**:
`𝐕(g^*ℱ) ≅ 𝐕(ℱ) ×_X T` as schemes over `T`. -/
@[ega "II 1.7.11"]
def vectorBundleBaseChangeIso :
    vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F) ≅
      (Over.pullback g).obj (vectorBundleOver X (F := F)) where
  hom := baseChangeHomEquiv g F _ (𝟙 _)
  inv := (baseChangeHomEquiv g F _).symm (𝟙 _)
  hom_inv_id := by
    apply (baseChangeHomEquiv g F _).injective
    rw [baseChangeHomEquiv_comp, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    rw [← baseChangeHomEquiv_comp, Category.comp_id, Equiv.apply_symm_apply]

/-- The base-change bijection is composition with the base-change isomorphism. -/
theorem baseChangeHomEquiv_eq (W : Over T)
    (u : W ⟶ vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F)) :
    baseChangeHomEquiv g F W u = u ≫ (vectorBundleBaseChangeIso g F).hom := by
  rw [← Category.comp_id u, baseChangeHomEquiv_comp, Category.comp_id]
  rfl

/-- **The base-change morphism `𝐕(g^*ℱ) ⟶ 𝐕(ℱ)`**, the second projection of the base-change
isomorphism. -/
def vectorBundleBaseChangeMap :
    vectorBundle T ((Scheme.Modules.pullback g).obj F) ⟶ vectorBundle X F :=
  (vectorBundleBaseChangeIso g F).hom.left ≫ pullback.fst _ _

/-- **The base-change square of a vector bundle is cartesian**:
`𝐕(g^*ℱ) = 𝐕(ℱ) ×_X T`, the maps being the base-change morphism and the two projections. -/
@[ega "II 1.7.11"]
theorem isPullback_vectorBundleBaseChangeMap :
    IsPullback (vectorBundleBaseChangeMap g F)
      (vectorBundleToBase T ((Scheme.Modules.pullback g).obj F)) (vectorBundleToBase X F) g := by
  refine (IsPullback.of_hasPullback (vectorBundleToBase X F) g).of_iso
    ((Over.forget T).mapIso (vectorBundleBaseChangeIso g F)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [vectorBundleBaseChangeMap]
  · have h := Over.w (vectorBundleBaseChangeIso g F).inv
    simp only [Iso.symm_hom, Functor.mapIso_inv, Over.forget_map,
      Iso.refl_hom, Category.comp_id]
    exact h.symm

/-- The base-change morphism as a morphism of schemes over `X`, out of `𝐕(g^*ℱ)` viewed over `X`
through `g`: the point of `𝐕(ℱ)` whose module morphism is the transpose of the tautological one. -/
def vectorBundleBaseChangeOver :
    (Over.map g).obj (vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F)) ⟶
      vectorBundleOver X (F := F) :=
  (vectorBundleHomEquiv F _).symm
    (transposeEquiv g F _ (vectorBundleHomEquiv _ _ (𝟙 _)))

/-- The base-change morphism `𝐕(g^*ℱ) ⟶ 𝐕(ℱ)` is the underlying morphism of schemes of
`vectorBundleBaseChangeOver`. -/
theorem vectorBundleBaseChangeMap_eq :
    vectorBundleBaseChangeMap g F = (vectorBundleBaseChangeOver g F).left := by
  have h : vectorBundleBaseChangeOver g F = ((Over.mapPullbackAdj g).homEquiv
      (vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F))
      (vectorBundleOver X (F := F))).symm (vectorBundleBaseChangeIso g F).hom :=
    (((Over.mapPullbackAdj g).homEquiv _ _).symm_apply_apply _).symm
  rw [h, Adjunction.homEquiv_counit]
  simp [vectorBundleBaseChangeMap]

/-- The base-change morphism over `X` commutes with the morphisms induced by a morphism of
modules. -/
theorem vectorBundleBaseChangeOver_naturality {G : X.Modules}
    [G.IsQuasicoherent] [((Scheme.Modules.pullback g).obj G).IsQuasicoherent] (f : F ⟶ G) :
    (Over.map g).map (vectorBundleMap T ((Scheme.Modules.pullback g).map f)) ≫
        vectorBundleBaseChangeOver g F =
      vectorBundleBaseChangeOver g G ≫ vectorBundleMap X f := by
  apply (vectorBundleHomEquiv F _).injective
  have hτ : vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj F) _
      (vectorBundleMap T ((Scheme.Modules.pullback g).map f)) =
      (Scheme.Modules.pullback g).map f ≫
        vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj G) _ (𝟙 _) :=
    (congrArg (vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj F) _)
      (Category.id_comp _).symm).trans (vectorBundleHomEquiv_comp_vectorBundleMap _ _ _)
  have hτ' : vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj F) _
      (vectorBundleMap T ((Scheme.Modules.pullback g).map f)) =
      vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj F) _ (𝟙 _) ≫
        AlgebraSheaf.underlyingModuleMap
          (pushforwardAlgebraMap (vectorBundleMap T ((Scheme.Modules.pullback g).map f))) :=
    (congrArg (vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj F) _)
      (Category.comp_id _).symm).trans (vectorBundleHomEquiv_comp _ _ _)
  have ht : transposeEquiv g F _ ((Scheme.Modules.pullback g).map f ≫
        vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj G) _ (𝟙 _)) =
      f ≫ transposeEquiv g G _ (vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj G) _ (𝟙 _)) :=
    (congrArg (· ≫ ((Scheme.Modules.pushforwardComp
        (vectorBundleOver T (F := (Scheme.Modules.pullback g).obj G)).hom g).app _).hom)
      (Adjunction.homEquiv_naturality_left (Scheme.Modules.pullbackPushforwardAdjunction g) f
        (vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj G) _ (𝟙 _)))).trans
      (Category.assoc _ _ _)
  refine (vectorBundleHomEquiv_comp_symm ((Over.map g).map
    (vectorBundleMap T ((Scheme.Modules.pullback g).map f))) _).trans ?_
  refine (transposeEquiv_comp g F (vectorBundleMap T ((Scheme.Modules.pullback g).map f))
    _).symm.trans ?_
  refine (congrArg (transposeEquiv g F _) (hτ'.symm.trans hτ)).trans ?_
  exact ht.trans (vectorBundleHomEquiv_symm_comp_vectorBundleMap f _ _).symm

/-- **The base-change morphism commutes with the morphisms induced by a morphism of modules**:
for `f : ℱ ⟶ 𝒢` the square `𝐕(g^*𝒢) ⟶ 𝐕(g^*ℱ) ⟶ 𝐕(ℱ)`, `𝐕(g^*𝒢) ⟶ 𝐕(𝒢) ⟶ 𝐕(ℱ)` commutes. -/
theorem vectorBundleMap_pullback_comp_vectorBundleBaseChangeMap {G : X.Modules}
    [G.IsQuasicoherent] [((Scheme.Modules.pullback g).obj G).IsQuasicoherent] (f : F ⟶ G) :
    (vectorBundleMap T ((Scheme.Modules.pullback g).map f)).left ≫
        vectorBundleBaseChangeMap g F =
      vectorBundleBaseChangeMap g G ≫ (vectorBundleMap X f).left := by
  rw [vectorBundleBaseChangeMap_eq, vectorBundleBaseChangeMap_eq]
  exact congrArg (fun h => h.left) (vectorBundleBaseChangeOver_naturality g F f)

end BaseChange


/-! ### The zero section, and the fibre of a surjection over it -/

section ZeroSection

variable {X : Scheme.{u}}

/-- **The zero section `o : X ⟶ 𝐕(ℱ)` as a morphism over `X`**, the point of `𝐕(ℱ)` over `𝟙 X`
whose module morphism is zero. The underlying morphism of schemes is the zero section that
`AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection` cuts out by the augmentation of
`Sym(ℱ)`; here it is read off the functor of points `vectorBundleHomEquiv`. -/
@[ega "II 1.7.9", sga "6 IX 1.6"]
def vectorBundleOverZeroSection (F : X.Modules) [F.IsQuasicoherent] :
    Over.mk (𝟙 X) ⟶ vectorBundleOver X (F := F) :=
  (vectorBundleHomEquiv F _).symm (0 : F ⟶ structurePushforward (𝟙 X))

/-- The module morphism of the zero section is zero. -/
theorem vectorBundleHomEquiv_vectorBundleOverZeroSection (F : X.Modules) [F.IsQuasicoherent] :
    vectorBundleHomEquiv F _ (vectorBundleOverZeroSection F) =
      (0 : F ⟶ structurePushforward (𝟙 X)) :=
  (vectorBundleHomEquiv F _).apply_symm_apply _

/-- The zero section is a section of the projection. -/
@[reassoc]
theorem vectorBundleOverZeroSection_left_comp (F : X.Modules) [F.IsQuasicoherent] :
    (vectorBundleOverZeroSection F).left ≫ vectorBundleToBase X F = 𝟙 X :=
  Over.w (vectorBundleOverZeroSection F)

/-- **A point factors through the zero section exactly when its module morphism vanishes.** The
module morphism of the composite of a morphism `W ⟶ X` with the zero section is zero. -/
@[ega "II 1.7.9" "partial"]
theorem vectorBundleHomEquiv_comp_vectorBundleOverZeroSection (F : X.Modules) [F.IsQuasicoherent]
    {W : Over X} (a : W ⟶ Over.mk (𝟙 X)) :
    vectorBundleHomEquiv F W (a ≫ vectorBundleOverZeroSection F) =
      (0 : F ⟶ structurePushforward W.hom) :=
  (vectorBundleHomEquiv_comp F a _).trans ((congrArg (· ≫ _)
    (vectorBundleHomEquiv_vectorBundleOverZeroSection F)).trans Limits.zero_comp)

variable {A B C : X.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent]
  [C.IsQuasicoherent] (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
  (hg : IsColimit (CokernelCofork.ofπ g w))

include w in
/-- The square of `AlgebraicGeometry.Scheme.Modules.isPullback_vectorBundleMap_zeroSection`
commutes, as a square of schemes over `X`. -/
theorem vectorBundleMap_comp_vectorBundleMap_eq_zeroSection :
    vectorBundleMap X g ≫ vectorBundleMap X f =
      Over.homMk (U := vectorBundleOver X (F := C)) (V := Over.mk (𝟙 X))
        (vectorBundleToBase X C) (Category.comp_id _) ≫ vectorBundleOverZeroSection A := by
  apply (vectorBundleHomEquiv A _).injective
  refine (vectorBundleHomEquiv_comp_vectorBundleMap f _ _).trans ?_
  refine Eq.trans ?_ (vectorBundleHomEquiv_comp_vectorBundleOverZeroSection A _).symm
  refine (congrArg (f ≫ ·) ((congrArg (vectorBundleHomEquiv B _) (Category.id_comp _).symm).trans
    (vectorBundleHomEquiv_comp_vectorBundleMap g _ _))).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) w).trans Limits.zero_comp)

variable {f g w} {W : Scheme.{u}} (x : W ⟶ vectorBundle X B) (y : W ⟶ X)
  (hxy : x ≫ (vectorBundleMap X f).left = y ≫ (vectorBundleOverZeroSection A).left)

include hxy in
/-- A point `x` of `𝐕(ℬ)` whose image in `𝐕(𝒜)` is `y` followed by the zero section lies over
`y`. -/
theorem cokernelFibre_comp_toBase : x ≫ vectorBundleToBase X B = y := by
  rw [← vectorBundleMap_left_comp X f, ← Category.assoc, hxy, Category.assoc,
    vectorBundleOverZeroSection_left_comp, Category.comp_id]

/-- The point of `𝐕(ℬ)` over `y` given by `x`, as a morphism of schemes over `X`. -/
def cokernelFibrePoint : Over.mk y ⟶ vectorBundleOver X (F := B) :=
  Over.homMk x (cokernelFibre_comp_toBase x y hxy)

include hxy in
/-- The module morphism of `cokernelFibrePoint x y hxy` vanishes on `𝒜`. -/
theorem comp_cokernelFibrePoint_eq_zero :
    f ≫ vectorBundleHomEquiv B (Over.mk y) (cokernelFibrePoint x y hxy) = 0 := by
  refine (vectorBundleHomEquiv_comp_vectorBundleMap f (Over.mk y)
    (cokernelFibrePoint x y hxy)).symm.trans ?_
  refine Eq.trans ?_ (vectorBundleHomEquiv_comp_vectorBundleOverZeroSection A
    (Over.homMk (U := Over.mk y) (V := Over.mk (𝟙 X)) y (Category.comp_id _)))
  exact congrArg (vectorBundleHomEquiv A (Over.mk y)) (Over.OverMorphism.ext hxy)

/-- The module morphism `𝒞 ⟶ y_* 𝒪_W` through which the module morphism of `x` factors. -/
def cokernelFibreDesc : C ⟶ structurePushforward y :=
  hg.desc (CokernelCofork.ofπ _ (comp_cokernelFibrePoint_eq_zero x y hxy))

omit [SheafOfModules.IsQuasicoherent C] in
/-- The module morphism of `cokernelFibrePoint x y hxy` is `g` followed by
`cokernelFibreDesc hg x y hxy`. -/
theorem cokernelFibreDesc_spec :
    g ≫ cokernelFibreDesc hg x y hxy =
      vectorBundleHomEquiv B (Over.mk y) (cokernelFibrePoint x y hxy) :=
  Cofork.IsColimit.π_desc hg

/-- **The lift to `𝐕(𝒞)`** of a point of `𝐕(ℬ)` lying over the zero section of `𝐕(𝒜)`. -/
def cokernelFibreLift : Over.mk y ⟶ vectorBundleOver X (F := C) :=
  (vectorBundleHomEquiv C (Over.mk y)).symm (cokernelFibreDesc hg x y hxy)

/-- The lift `cokernelFibreLift hg x y hxy` composed with `𝐕(𝒞) ⟶ 𝐕(ℬ)` is the point given by
`x`. -/
theorem cokernelFibreLift_comp :
    cokernelFibreLift hg x y hxy ≫ vectorBundleMap X g = cokernelFibrePoint x y hxy := by
  apply (vectorBundleHomEquiv B (Over.mk y)).injective
  exact (vectorBundleHomEquiv_symm_comp_vectorBundleMap g (Over.mk y) _).trans
    (cokernelFibreDesc_spec hg x y hxy)

/-- A morphism `Over.mk y ⟶ 𝐕(𝒞)` whose composite with `𝐕(𝒞) ⟶ 𝐕(ℬ)` is `x` equals
`cokernelFibreLift hg x y hxy`. -/
theorem cokernelFibreLift_unique (m : Over.mk y ⟶ vectorBundleOver X (F := C))
    (hm : m.left ≫ (vectorBundleMap X g).left = x) : m = cokernelFibreLift hg x y hxy := by
  refine ((vectorBundleHomEquiv C (Over.mk y)).symm_apply_apply m).symm.trans
    (congrArg (vectorBundleHomEquiv C (Over.mk y)).symm ?_)
  refine Cofork.IsColimit.hom_ext hg ?_
  refine (vectorBundleHomEquiv_comp_vectorBundleMap g (Over.mk y) m).symm.trans ?_
  refine Eq.trans ?_ (cokernelFibreDesc_spec hg x y hxy).symm
  exact congrArg (vectorBundleHomEquiv B (Over.mk y)) (Over.OverMorphism.ext hm)

variable (f g w) in
include hg in
/-- **The vector bundle of a cokernel is the fibre over the zero section.** For `ℬ ⟶ 𝒞` the
cokernel of `𝒜 ⟶ ℬ`, the square formed by `𝐕(𝒞) ⟶ 𝐕(ℬ)`, the projection `𝐕(𝒞) ⟶ X`, the zero
section `X ⟶ 𝐕(𝒜)` and `𝐕(ℬ) ⟶ 𝐕(𝒜)` is cartesian: a point of `𝐕(ℬ)` lies over the zero section of
`𝐕(𝒜)` exactly when its module morphism kills `𝒜`, that is factors through `𝒞`. -/
theorem isPullback_vectorBundleMap_zeroSection :
    IsPullback (vectorBundleMap X g).left (vectorBundleToBase X C) (vectorBundleMap X f).left
      (vectorBundleOverZeroSection A).left :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (congrArg (fun h => h.left) (vectorBundleMap_comp_vectorBundleMap_eq_zeroSection f g w))
    (fun s => (cokernelFibreLift hg s.fst s.snd s.condition).left)
    (fun s => congrArg (fun h => h.left) (cokernelFibreLift_comp hg s.fst s.snd s.condition))
    (fun s => Over.w (cokernelFibreLift hg s.fst s.snd s.condition))
    (fun s m h₁ h₂ => congrArg (fun h => h.left)
      (cokernelFibreLift_unique hg s.fst s.snd s.condition (Over.homMk m h₂) h₁)))

/-- **The morphism induced by a morphism of modules carries the zero section to the zero
section.** -/
theorem vectorBundleOverZeroSection_comp_vectorBundleMap {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (f : F ⟶ G) :
    vectorBundleOverZeroSection G ≫ vectorBundleMap X f = vectorBundleOverZeroSection F := by
  apply (vectorBundleHomEquiv F _).injective
  exact (vectorBundleHomEquiv_symm_comp_vectorBundleMap f _ _).trans
    (Limits.comp_zero.trans (vectorBundleHomEquiv_vectorBundleOverZeroSection F).symm)

/-- Transposition along `g` carries the zero morphism to the zero morphism. -/
theorem transposeEquiv_zero {T : Scheme.{u}} (g : T ⟶ X) (F : X.Modules) [F.IsQuasicoherent]
    (W : Over T) :
    transposeEquiv g F W 0 = 0 := by
  rw [transposeEquiv_apply, Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero,
    Limits.zero_comp]

/-- **The base-change morphism carries the zero section to the zero section**: for `g : T ⟶ X`,
the zero section of `𝐕(g^*ℱ)` followed by `𝐕(g^*ℱ) ⟶ 𝐕(ℱ)` is `g` followed by the zero section
of `𝐕(ℱ)`. -/
theorem vectorBundleOverZeroSection_comp_vectorBundleBaseChangeMap {T : Scheme.{u}} (g : T ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] [((Scheme.Modules.pullback g).obj F).IsQuasicoherent] :
    (vectorBundleOverZeroSection ((Scheme.Modules.pullback g).obj F)).left ≫
        vectorBundleBaseChangeMap g F =
      g ≫ (vectorBundleOverZeroSection F).left := by
  rw [vectorBundleBaseChangeMap_eq]
  let o' := vectorBundleOverZeroSection ((Scheme.Modules.pullback g).obj F)
  let a := (Over.map g).map o'
  let τ := vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj F)
    (vectorBundleOver T (F := (Scheme.Modules.pullback g).obj F)) (𝟙 _)
  have h4 : τ ≫ AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap o') =
      (0 : (Scheme.Modules.pullback g).obj F ⟶ structurePushforward (𝟙 T)) :=
    (vectorBundleHomEquiv_comp ((Scheme.Modules.pullback g).obj F) o' (𝟙 _)).symm.trans
      ((congrArg (vectorBundleHomEquiv ((Scheme.Modules.pullback g).obj F) (Over.mk (𝟙 T)))
        (Category.comp_id o')).trans
        (vectorBundleHomEquiv_vectorBundleOverZeroSection ((Scheme.Modules.pullback g).obj F)))
  have h : a ≫ vectorBundleBaseChangeOver g F =
      Over.homMk (U := (Over.map g).obj (Over.mk (𝟙 T))) (V := Over.mk (𝟙 X)) g
        (by simp) ≫ vectorBundleOverZeroSection F := by
    apply (vectorBundleHomEquiv F ((Over.map g).obj (Over.mk (𝟙 T)))).injective
    refine (vectorBundleHomEquiv_comp_symm a _).trans ?_
    refine Eq.trans ?_ (vectorBundleHomEquiv_comp_vectorBundleOverZeroSection F _).symm
    refine (transposeEquiv_comp g F o' τ).symm.trans ?_
    exact (congrArg (transposeEquiv g F (Over.mk (𝟙 T))) h4).trans (transposeEquiv_zero g F _)
  exact congrArg (fun h => h.left) h

end ZeroSection

end AlgebraicGeometry.Scheme.Modules

end
