module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms

/-!
# Axiom (A5) descends along a field extension

For a field extension `k'/k` the base change functor `X ↦ X_{k'}` carries the point `Spec k` to
the point `Spec k'` and the product `X × Y = X ×_k Y` to the product `X_{k'} × Y_{k'}` over `k'`,
compatibly with the projections. Through the comparison isomorphisms of Tag 0FVT the Künneth map
of `H^*` extended to `F'` is the Künneth map of `(H')^*`, so (A5) for `(H')^*` gives (A5) for
`H^*` by the linear algebra of the proof of (A1).

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.baseChangePointIso`: `(Spec k)_{k'} ≅ Spec k'`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.baseChangeProdIso`:
  `(X × Y)_{k'} ≅ X_{k'} × Y_{k'}`.

## Main results

* `Stacks.WeilCohomology.FieldExtensionComparison.iso_kunnethMap`: the comparison isomorphisms
  intertwine the two Künneth maps.
* `Stacks.WeilCohomology.FieldExtensionComparison.kunnethAxiom`: (A5) descends.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- An isomorphism of the underlying schemes over `k` is an isomorphism of smooth projective
schemes. -/
def isoOfSchemeIso {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (e : (toScheme k).obj X ≅ (toScheme k).obj Y)
    (he : e.hom ≫ Y.obj.hom = X.obj.hom) : X ≅ Y :=
  ObjectProperty.isoMk _ (Over.isoMk e he)

/-- The underlying morphism of schemes of `isoOfSchemeIso e he` is `e.hom`. -/
@[simp]
theorem map_isoOfSchemeIso_hom {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (e : (toScheme k).obj X ≅ (toScheme k).obj Y) (he : e.hom ≫ Y.obj.hom = X.obj.hom) :
    (toScheme k).map (isoOfSchemeIso e he).hom = e.hom :=
  rfl

/-- The pullback of the identity of `Spec k` along `Spec k' ⟶ Spec k` is `Spec k'`. -/
def pullbackIdSpecIso :
    Limits.pullback (𝟙 (Spec (.of k))) (ArtinSchreier.specExt k k') ≅ Spec (.of k') where
  hom := pullback.snd _ _
  inv := pullback.lift (ArtinSchreier.specExt k k') (𝟙 _) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact (pullback.condition (f := 𝟙 (Spec (.of k)))
        (g := ArtinSchreier.specExt k k')).symm.trans (Category.comp_id _)
    · simp
  inv_hom_id := pullback.lift_snd _ _ _

/-- The scheme isomorphism `(Spec k) ×_k k' ≅ Spec k'`. -/
def baseChangePointSchemeIso :
    (toScheme k').obj ((baseChange k k').obj (point k)) ≅ (toScheme k').obj (point k') :=
  pullbackIdSpecIso

/-- **`(Spec k)_{k'} ≅ Spec k'`**, as smooth projective schemes over `k'`. -/
def baseChangePointIso : (baseChange k k').obj (point k) ≅ point k' :=
  isoOfSchemeIso baseChangePointSchemeIso (Category.comp_id _)

variable (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- The square exhibiting `(X × Y)_{k'}` as the product of `X_{k'}` and `Y_{k'}` over `k'`. -/
theorem isPullback_baseChange_prod :
    IsPullback ((toScheme k').map ((baseChange k k').map (fst X Y)))
      ((toScheme k').map ((baseChange k k').map (snd X Y)))
      ((baseChange k k').obj X).obj.hom ((baseChange k k').obj Y).obj.hom := by
  have h1 := isPullback_baseChange_map (k' := k') (snd X Y)
  have h2 : IsPullback ((toScheme k).map (snd X Y)) ((toScheme k).map (fst X Y)) Y.obj.hom
      X.obj.hom := (IsPullback.of_hasPullback X.obj.hom Y.obj.hom).flip
  have h3 := h1.paste_vert h2
  rw [← baseChangeProj_naturality (fst X Y), (isPullback_baseChangeProj (k' := k') Y).w] at h3
  refine IsPullback.of_right h3.flip ?_ (isPullback_baseChangeProj X)
  rw [w, w]

/-- The scheme isomorphism `(X × Y)_{k'} ≅ X_{k'} ×_{k'} Y_{k'}`. -/
def baseChangeProdSchemeIso :
    (toScheme k').obj ((baseChange k k').obj (prod X Y)) ≅
      (toScheme k').obj (prod ((baseChange k k').obj X) ((baseChange k k').obj Y)) :=
  (isPullback_baseChange_prod X Y).isoPullback

/-- The scheme isomorphism `(X × Y)_{k'} ≅ X_{k'} ×_{k'} Y_{k'}` followed by the first projection
is the base change of the first projection of `X × Y`. -/
@[reassoc]
theorem baseChangeProdSchemeIso_hom_fst :
    (baseChangeProdSchemeIso (k' := k') X Y).hom ≫
        (toScheme k').map (fst ((baseChange k k').obj X) ((baseChange k k').obj Y)) =
      (toScheme k').map ((baseChange k k').map (fst X Y)) :=
  IsPullback.isoPullback_hom_fst _

/-- The scheme isomorphism `(X × Y)_{k'} ≅ X_{k'} ×_{k'} Y_{k'}` followed by the second projection
is the base change of the second projection of `X × Y`. -/
@[reassoc]
theorem baseChangeProdSchemeIso_hom_snd :
    (baseChangeProdSchemeIso (k' := k') X Y).hom ≫
        (toScheme k').map (snd ((baseChange k k').obj X) ((baseChange k k').obj Y)) =
      (toScheme k').map ((baseChange k k').map (snd X Y)) :=
  IsPullback.isoPullback_hom_snd _

/-- **`(X × Y)_{k'} ≅ X_{k'} × Y_{k'}`**, as smooth projective schemes over `k'`. -/
def baseChangeProdIso :
    (baseChange k k').obj (prod X Y) ≅ prod ((baseChange k k').obj X) ((baseChange k k').obj Y) :=
  isoOfSchemeIso (baseChangeProdSchemeIso X Y) (by
    calc (baseChangeProdSchemeIso X Y).hom ≫ (prod ((baseChange k k').obj X)
          ((baseChange k k').obj Y)).obj.hom =
        (baseChangeProdSchemeIso X Y).hom ≫ ((toScheme k').map
          (fst ((baseChange k k').obj X) ((baseChange k k').obj Y)) ≫
            ((baseChange k k').obj X).obj.hom) := by rw [w]
      _ = _ := by rw [← Category.assoc, baseChangeProdSchemeIso_hom_fst, w])

/-- `(X × Y)_{k'} ≅ X_{k'} × Y_{k'}` followed by the first projection is the base change of the
first projection of `X × Y`. -/
@[reassoc (attr := simp)]
theorem baseChangeProdIso_hom_fst :
    (baseChangeProdIso (k' := k') X Y).hom ≫ fst _ _ = (baseChange k k').map (fst X Y) :=
  hom_ext' (by rw [CategoryTheory.Functor.map_comp]; exact baseChangeProdSchemeIso_hom_fst X Y)

/-- `(X × Y)_{k'} ≅ X_{k'} × Y_{k'}` followed by the second projection is the base change of the
second projection of `X × Y`. -/
@[reassoc (attr := simp)]
theorem baseChangeProdIso_hom_snd :
    (baseChangeProdIso (k' := k') X Y).hom ≫ snd _ _ = (baseChange k k').map (snd X Y) :=
  hom_ext' (by rw [CategoryTheory.Functor.map_comp]; exact baseChangeProdSchemeIso_hom_snd X Y)

end SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- **The comparison isomorphisms intertwine the Künneth maps**: the image of `p^*a ∪ q^*b` in
`(H')^*((X × Y)_{k'})` is the pullback along `(X × Y)_{k'} ≅ X_{k'} × Y_{k'}` of
`p'^*a' ∪ q'^*b'`, for the images `a'`, `b'` of `a`, `b`. -/
theorem iso_kunnethMap (X Y : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) (b : 𝔇.H Y) :
    Φ.ρ (prod X Y) (𝔇.kunnethMap X Y (a ⊗ₜ b)) =
      𝔇'.pull (baseChangeProdIso X Y).hom
        (𝔇'.kunnethMap ((baseChange k k').obj X) ((baseChange k k').obj Y)
          (Φ.ρ X a ⊗ₜ Φ.ρ Y b)) := by
  have h1 : ∀ x, 𝔇'.pull (baseChangeProdIso X Y).hom (𝔇'.pull (fst _ _) x) =
      𝔇'.pull ((baseChange k k').map (fst X Y)) x := fun x => by
    rw [← baseChangeProdIso_hom_fst, 𝔇'.pull_comp]; rfl
  have h2 : ∀ x, 𝔇'.pull (baseChangeProdIso X Y).hom (𝔇'.pull (snd _ _) x) =
      𝔇'.pull ((baseChange k k').map (snd X Y)) x := fun x => by
    rw [← baseChangeProdIso_hom_snd, 𝔇'.pull_comp]; rfl
  rw [FirstChernClassData.kunnethMap_tmul, FirstChernClassData.kunnethMap_tmul, map_mul, map_mul,
    h1, h2, ρ_apply, ρ_apply, ρ_apply, ρ_apply, Φ.iso_natural, Φ.iso_natural]

/-- An `F`-linear map is bijective once its base change to `F'`, followed by a linear
isomorphism, is. -/
private theorem bijective_of_bijective_comp_baseChange {M N P : Type*} [AddCommGroup M]
    [Module F M] [AddCommGroup N] [Module F N] [AddCommGroup P] [Module F' P]
    (g : M →ₗ[F] N) (f : F' ⊗[F] N ≃ₗ[F'] P) (hb : Bijective (f.toLinearMap ∘ₗ g.baseChange F')) :
    Bijective g :=
  bijective_of_bijective_baseChange F' g ((Bijective.of_comp_iff' f.bijective _).mp hb)

include Φ in
/-- **Axiom (A5) descends**: if `(H')^*` is compatible with finite products, so is `H^*`. -/
theorem kunnethAxiom (h : 𝔇'.KunnethAxiom) : 𝔇.KunnethAxiom := by
  refine ⟨?_, fun X Y => ?_⟩
  · -- `H^*(Spec k) = F`
    let pt := point k
    have key : (Φ.iso pt).toLinearMap ∘ₗ (Algebra.linearMap F (𝔇.H pt)).baseChange F' =
        (𝔇'.pull (baseChangePointIso (k := k) (k' := k')).hom).toLinearMap ∘ₗ
          (Algebra.linearMap F' (𝔇'.H (point k'))) ∘ₗ
            (TensorProduct.AlgebraTensorModule.rid F F' F').toLinearMap := by
      refine LinearMap.ext fun t => t.inductionOn (fun c x => ?_)
        (fun x y hx hy => by simp only [map_add] at hx hy ⊢; rw [hx, hy])
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul,
        Algebra.linearMap_apply, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.rid_tmul, AlgHom.toLinearMap_apply, AlgHom.commutes]
      show Φ.iso pt (c ⊗ₜ algebraMap F (𝔇.H pt) x) = algebraMap F' _ (x • c)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        show (x • c) ⊗ₜ[F] (1 : 𝔇.H pt) = (x • c) • (1 : F' ⊗[F] 𝔇.H pt) by
          rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    refine bijective_of_bijective_comp_baseChange _ (Φ.iso pt).toLinearEquiv ?_
    rw [key]
    exact (𝔇'.bijective_pull_of_iso _).comp
      (h.1.comp (TensorProduct.AlgebraTensorModule.rid F F' F').bijective)
  · -- the Künneth map
    set X' := (baseChange k k').obj X
    set Y' := (baseChange k k').obj Y
    let e : F' ⊗[F] (𝔇.H X ⊗[F] 𝔇.H Y) ≃ₗ[F'] 𝔇'.H X' ⊗[F'] 𝔇'.H Y' :=
      (TensorProduct.AlgebraTensorModule.distribBaseChange F F' (𝔇.H X) (𝔇.H Y)).trans
        (TensorProduct.congr (Φ.iso X).toLinearEquiv (Φ.iso Y).toLinearEquiv)
    have key : (Φ.iso (prod X Y)).toLinearMap ∘ₗ (𝔇.kunnethMap X Y).baseChange F' =
        (𝔇'.pull (baseChangeProdIso X Y).hom).toLinearMap ∘ₗ 𝔇'.kunnethMap X' Y' ∘ₗ
          e.toLinearMap := by
      refine LinearMap.ext fun x => x.inductionOn (fun c t => ?_)
        (fun x y hx hy => by simp only [map_add] at hx hy ⊢; rw [hx, hy])
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | tmul a b =>
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, e,
          LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
          AlgEquiv.toLinearEquiv_apply, AlgHom.toLinearMap_apply]
        rw [iso_tmul, ← ρ_apply, iso_tmul, ← ρ_apply, ← ρ_apply, Φ.iso_kunnethMap,
          ← TensorProduct.smul_tmul', map_smul, map_smul]
    refine bijective_of_bijective_comp_baseChange _ (Φ.iso (prod X Y)).toLinearEquiv ?_
    rw [key]
    exact (𝔇'.bijective_pull_of_iso _).comp ((h.2 X' Y').comp e.bijective)

end FieldExtensionComparison

end Stacks.WeilCohomology
