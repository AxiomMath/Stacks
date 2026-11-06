module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Units

/-!
# Base change for the direct image over affine schemes

For ring maps `A ⟶ B` and `A ⟶ A'`, the square of spectra
```
Spec (B ⊗[A] A') --g'--> Spec B
|f'                      |f
Spec A'          --g-->   Spec A
```
is cartesian, and the base-change morphism `g^* f_* ⟶ f'_* (g')^*` of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` ought to be invertible at every
quasi-coherent module.  This file assembles that statement: it reduces invertibility to
bijectivity on global sections, exhibits the resulting comparison of `A'`-modules
`A' ⊗[A] Γ(𝓕, ⊤) ⟶ (B ⊗[A] A') ⊗[B] Γ(𝓕, ⊤)`, and proves that any `A'`-linear map of that shape
which carries `1 ⊗ m` to `1 ⊗ m` is bijective.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.tildeΓIso`: a quasi-coherent module on
  `Spec R` is the module associated to its global sections.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.tensorCancel`: the inverse of the affine
  base-change comparison, `(b ⊗ a') ⊗ m ↦ a' ⊗ b • m`.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.sectionsComparison`: the comparison of
  `A'`-modules `A' ⊗[A] Γ(𝓕, ⊤) ⟶ (B ⊗[A] A') ⊗[B] Γ(𝓕, ⊤)` on global sections.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.sectionsPullbackIso_hom_unit`: under the
  identification of the global sections of the inverse image along `Spec.map φ` with
  `T ⊗_R Γ(𝓕, ⊤)`, the unit of the pullback--pushforward adjunction is `m ↦ 1 ⊗ m`.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.bijective_of_one_tmul`: an `A'`-linear map
  `A' ⊗[A] M ⟶ (B ⊗[A] A') ⊗[B] M` carrying `1 ⊗ m` to `1 ⊗ m` is bijective.
* `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.specTensor_square`: the square of spectra
  above commutes.
* `isIso_baseChangeNatTrans_specTensor_of_bijective`: the base-change morphism is invertible as
  soon as it is bijective on global sections.

## Implementation notes

`tildeΓIso` is written through `AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans` rather than
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ`, matching the components of
`Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso`. The middle object of that composite
is `(tilde.functor R).obj (moduleSpecΓFunctor.obj 𝓕)` in one spelling and
`tilde ((modulesSpecToSheaf.obj 𝓕).presheaf.obj (op ⊤))` in the other, and the two are
interconvertible only by unfolding a semireducible definition, which `simp` and `rw` will not do.
With the components in the first spelling the composite can be taken apart by `Iso.trans_hom`.

The module-theoretic half is phrased throughout in terms of `ModuleCat.extendScalars` and
`ModuleCat.restrictScalars`, whose module structures are `Module.compHom` of the given ring map.
Those are *not* definitionally the `Algebra`-derived structures, so the tensor products appearing
here are not the ones `TensorProduct.AlgebraTensorModule.cancelBaseChange` is stated for; the
inverse comparison is therefore built by hand from `TensorProduct.liftAddHom`, which needs no
module structure on its target.  For the same reason pure tensors are introduced through the
abbreviations `tmulA` and `tmulB`: a tensor written twice with different expected types picks up
different instance paths and the two terms are then not syntactically equal, which defeats `rw`.
`toRestrictScalars` and `ofRestrictScalars` are the identity on elements, present only to put a
syntactic marker on the module structure in play.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChangeLocality

variable {R T : CommRingCat.{u}} (φ : R ⟶ T)

/-- A quasi-coherent module on an affine scheme is the module associated to its global
sections. -/
noncomputable def tildeΓIso (F : (Spec R).Modules) [F.IsQuasicoherent] :
    (tilde.functor R).obj (moduleSpecΓFunctor.obj F) ≅ F :=
  @asIso _ _ _ _ (Scheme.Modules.fromTildeΓNatTrans.app F)
    (show IsIso (Scheme.Modules.fromTildeΓ F) from inferInstance)

/-- On global sections, the inverse of `tildeΓIso F` is the unit `Γ(F, ⊤) ⟶ Γ(Γ(F, ⊤)^~, ⊤)`. -/
theorem moduleSpecΓFunctor_map_tildeΓIso_inv (F : (Spec R).Modules) [F.IsQuasicoherent] :
    moduleSpecΓFunctor.map (tildeΓIso F).inv =
      tilde.toTildeΓNatIso.hom.app (moduleSpecΓFunctor.obj F) := by
  rw [← Functor.mapIso_inv]
  exact ((Iso.comp_hom_eq_id _).mp
    (tilde.adjunction.right_triangle_components F)).symm

open SectionsColimit in
/-- Under the identification `SectionsColimit.sectionsPullbackIso` of the global sections of the
inverse image of `F` along `Spec.map φ` with `T ⊗_R Γ(F, ⊤)`, the unit of the
pullback--pushforward adjunction sends `m` to `1 ⊗ m`. -/
theorem sectionsPullbackIso_hom_unit (F : (Spec R).Modules) [F.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj F)
    (y : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj F))
    (hy : (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app F)).hom x = y) :
    (SectionsColimit.sectionsPullbackIso φ F).hom.hom y = (1 : T) ⊗ₜ[R, φ.hom] x := by
  have hnat := congr(moduleSpecΓFunctor.map
    $((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
      (tildeΓIso F).inv))
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have hnat' := congr(ModuleCat.Hom.hom $hnat x)
  simp only [Functor.id_map, ModuleCat.hom_comp, LinearMap.comp_apply] at hnat'
  have h3 : (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback (Spec.map φ)).map (tildeΓIso F).inv)).hom y =
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map φ)).unit.app ((tilde.functor R).obj (moduleSpecΓFunctor.obj F)))).hom
        ((tilde.toTildeΓNatIso.hom.app (moduleSpecΓFunctor.obj F)).hom x) := by
    rw [← moduleSpecΓFunctor_map_tildeΓIso_inv, hnat', ← hy]
    rfl
  have hdef : SectionsColimit.sectionsPullbackIso φ F =
      moduleSpecΓFunctor.mapIso
          ((Scheme.Modules.pullback (Spec.map φ)).mapIso (tildeΓIso F).symm) ≪≫
        tildeSectionsPullbackIso φ (moduleSpecΓFunctor.obj F) := rfl
  rw [hdef]
  simp only [tildeSectionsPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h3, AffineBaseChange.tildePullbackIso_unit φ (moduleSpecΓFunctor.obj F) x]
  exact congr(ModuleCat.Hom.hom
    $((tilde.toTildeΓNatIso.app
        ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj F))).hom_inv_id)
    ((1 : T) ⊗ₜ[R, φ.hom] x))


section Core

/-- Restriction of scalars does not change the underlying set: this is the identity map on
elements, written so that its target carries the restricted module structure. -/
def toRestrictScalars {R S : Type u} [Ring R] [Ring S] (f : R →+* S) {M : ModuleCat.{u} S}
    (m : M) : (ModuleCat.restrictScalars f).obj M := m

/-- The identity map inverse to `toRestrictScalars`. -/
def ofRestrictScalars {R S : Type u} [Ring R] [Ring S] (f : R →+* S) {M : ModuleCat.{u} S}
    (m : (ModuleCat.restrictScalars f).obj M) : M := m

/-- The identity map from `S`, viewed as an `R`-module by restriction of scalars along
`f : R →+* S`, to the ring `S` itself. -/
def ofRestrictScalarsSelf {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (x : (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) : S := x

variable {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
  [Algebra A B] [Algebra A A'] {M : ModuleCat.{u} B}

/-! ### Pure tensors on the two sides of the comparison -/

/-- The pure tensor `a' ⊗ m` of `A' ⊗[A] M`, where `M` is an `A`-module by restriction of
scalars along `A → B`. -/
noncomputable def tmulA (a' : A') (y : M) :
    (ModuleCat.extendScalars (algebraMap A A')).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M) :=
  toRestrictScalars (algebraMap A A') (M := ModuleCat.of A' A') a' ⊗ₜ
    toRestrictScalars (algebraMap A B) y

/-- The pure tensor `w ⊗ m` of `(B ⊗[A] A') ⊗[B] M`. -/
noncomputable def tmulB (w : B ⊗[A] A') (y : M) :
    (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))).obj M :=
  w ⊗ₜ[B, Algebra.TensorProduct.includeLeftRingHom] y

/-- `a' ⊗ (m₁ + m₂) = a' ⊗ m₁ + a' ⊗ m₂` in `A' ⊗[A] M`. -/
theorem tmulA_add_right (a' : A') (y₁ y₂ : M) :
    tmulA (A := A) a' (y₁ + y₂) = tmulA a' y₁ + tmulA a' y₂ :=
  TensorProduct.tmul_add _ _ _

/-- `(a₁ + a₂) ⊗ m = a₁ ⊗ m + a₂ ⊗ m` in `A' ⊗[A] M`. -/
theorem tmulA_add_left (a₁ a₂ : A') (y : M) :
    tmulA (A := A) (a₁ + a₂) y = tmulA a₁ y + tmulA a₂ y :=
  TensorProduct.add_tmul _ _ _

/-- `a₁ • (a₂ ⊗ m) = (a₁ * a₂) ⊗ m` in `A' ⊗[A] M`. -/
theorem smul_tmulA (a₁ a₂ : A') (y : M) :
    a₁ • tmulA (A := A) a₂ y = tmulA (a₁ * a₂) y := rfl

/-- `0 ⊗ m = 0` in `(B ⊗[A] A') ⊗[B] M`. -/
theorem tmulB_zero_left (y : M) : tmulB (A' := A') (0 : B ⊗[A] A') y = 0 :=
  TensorProduct.zero_tmul _ _

/-- `(w₁ + w₂) ⊗ m = w₁ ⊗ m + w₂ ⊗ m` in `(B ⊗[A] A') ⊗[B] M`. -/
theorem tmulB_add_left (w₁ w₂ : B ⊗[A] A') (y : M) :
    tmulB (w₁ + w₂) y = tmulB w₁ y + tmulB w₂ y :=
  TensorProduct.add_tmul _ _ _

/-- `c • (w ⊗ m) = (c * w) ⊗ m` in `(B ⊗[A] A') ⊗[B] M`. -/
theorem smul_tmulB (c w : B ⊗[A] A') (y : M) : c • tmulB w y = tmulB (c * w) y := rfl

/-- `w ⊗ b • m = ((b ⊗ 1) * w) ⊗ m` in `(B ⊗[A] A') ⊗[B] M`. -/
theorem tmulB_smul (b : B) (w : B ⊗[A] A') (y : M) :
    tmulB w (b • y) = tmulB (Algebra.TensorProduct.includeLeftRingHom b * w) y :=
  (TensorProduct.smul_tmul (R := B) b
    (toRestrictScalars (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))
      (M := ModuleCat.of (B ⊗[A] A') (B ⊗[A] A')) w) y).symm

/-- `((b ⊗ 1) * (1 ⊗ a')) ⊗ m = (b ⊗ a') ⊗ m` in `(B ⊗[A] A') ⊗[B] M`. -/
theorem tmulB_tmul_mul (b : B) (a' : A') (y : M) :
    tmulB (Algebra.TensorProduct.includeLeftRingHom b *
        (Algebra.TensorProduct.includeRight a' : B ⊗[A] A')) y =
      tmulB (b ⊗ₜ a' : B ⊗[A] A') y := by
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-! ### The inverse comparison -/

/-- The additive map `m ↦ a' ⊗ b • m` from `M` to `A' ⊗[A] M`. -/
noncomputable def smulTmul (b : B) (a' : A') :
    ((ModuleCat.restrictScalars (algebraMap A B)).obj M →+
      (ModuleCat.extendScalars (algebraMap A A')).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :=
  AddMonoidHom.mk'
    (fun n => tmulA a' (b • ofRestrictScalars (algebraMap A B) n))
    (fun n₁ n₂ => by
      rw [show b • ofRestrictScalars (algebraMap A B) (n₁ + n₂) =
            b • ofRestrictScalars (algebraMap A B) n₁ + b • ofRestrictScalars (algebraMap A B) n₂
        from smul_add b _ _]
      exact tmulA_add_right _ _ _)

/-- `smulTmul b a'` sends `m` to `a' ⊗ b • m`. -/
@[simp]
theorem smulTmul_apply (b : B) (a' : A')
    (n : (ModuleCat.restrictScalars (algebraMap A B)).obj M) :
    smulTmul (M := M) b a' n = tmulA a' (b • ofRestrictScalars (algebraMap A B) n) := rfl

/-- The additive bilinear data `b ⊗ a' ↦ (m ↦ a' ⊗ b • m)`. -/
noncomputable def smulTmulBilin :
    B →+ (A' →+ ((ModuleCat.restrictScalars (algebraMap A B)).obj M →+
      (ModuleCat.extendScalars (algebraMap A A')).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj M))) :=
  AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun a' => smulTmul b a')
      (fun a₁ a₂ => by
        ext n
        simp only [AddMonoidHom.add_apply, smulTmul_apply]
        exact tmulA_add_left _ _ _))
    (fun b₁ b₂ => by
      ext a' n
      simp only [AddMonoidHom.add_apply, AddMonoidHom.mk'_apply, smulTmul_apply]
      rw [show (b₁ + b₂) • ofRestrictScalars (algebraMap A B) n =
            b₁ • ofRestrictScalars (algebraMap A B) n + b₂ • ofRestrictScalars (algebraMap A B) n
        from add_smul _ _ _]
      exact tmulA_add_right _ _ _)

/-- `(b ⊗ a') ↦ (m ↦ a' ⊗ b • m)`, on `B ⊗[A] A'`. -/
noncomputable def smulTmulLift :
    (B ⊗[A] A') →+ ((ModuleCat.restrictScalars (algebraMap A B)).obj M →+
      (ModuleCat.extendScalars (algebraMap A A')).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :=
  TensorProduct.liftAddHom smulTmulBilin (fun a b a' => by
    ext n
    simp only [smulTmulBilin, AddMonoidHom.mk'_apply, smulTmul_apply, tmulA]
    rw [Algebra.smul_def a b, mul_smul, Algebra.smul_def a a']
    exact (TensorProduct.smul_tmul a
      (toRestrictScalars (algebraMap A A') (M := ModuleCat.of A' A') a')
      (toRestrictScalars (algebraMap A B) (b • ofRestrictScalars (algebraMap A B) n))).symm)

/-- `smulTmulLift ((b ⊗ 1) * z)` sends `m` to `smulTmulLift z (b • m)`. -/
theorem smulTmulLift_includeLeft_mul (b : B) (z : B ⊗[A] A')
    (n : (ModuleCat.restrictScalars (algebraMap A B)).obj M) :
    smulTmulLift (M := M) (Algebra.TensorProduct.includeLeftRingHom b * z) n =
      smulTmulLift z (toRestrictScalars (algebraMap A B)
        (b • ofRestrictScalars (algebraMap A B) n)) := by
  induction z with
  | tmul b₀ a' =>
      rw [Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [smulTmulLift, TensorProduct.liftAddHom_tmul, smulTmulBilin,
        AddMonoidHom.mk'_apply, smulTmul_apply]
      rw [mul_comm b b₀, mul_smul]
      rfl
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, map_add, AddMonoidHom.add_apply,
      AddMonoidHom.add_apply, h₁, h₂]

/-- The inverse of the affine base-change comparison: `(b ⊗ a') ⊗ m ↦ a' ⊗ b • m`. -/
noncomputable def tensorCancel :
    (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))).obj M →+
      (ModuleCat.extendScalars (algebraMap A A')).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj M) :=
  TensorProduct.liftAddHom smulTmulLift fun b z n => smulTmulLift_includeLeft_mul b z n

/-- `tensorCancel` sends `(b ⊗ a') ⊗ m` to `a' ⊗ b • m`. -/
theorem tensorCancel_tmulB (b : B) (a' : A') (y : M) :
    tensorCancel (tmulB (b ⊗ₜ a' : B ⊗[A] A') y) = tmulA a' (b • y) := rfl

/-- `tensorCancel` sends `(1 ⊗ a') ⊗ m` to `a' ⊗ m`. -/
theorem tensorCancel_tmulB_includeRight (a' : A') (y : M) :
    tensorCancel (tmulB (Algebra.TensorProduct.includeRight a' : B ⊗[A] A') y) = tmulA a' y := by
  rw [Algebra.TensorProduct.includeRight_apply, tensorCancel_tmulB, one_smul]

/-- An additive endomorphism of a tensor product fixing all pure tensors is the identity. -/
private theorem addMonoidHom_apply_eq_self_of_tmul {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] (f : M ⊗[R] N →+ M ⊗[R] N)
    (h : ∀ (x : M) (y : N), f (x ⊗ₜ y) = x ⊗ₜ y) (z : M ⊗[R] N) : f z = z :=
  TensorProduct.inductionOn z h fun u v hu hv => by rw [map_add, hu, hv]

/-! ### Bijectivity of the comparison -/

section Comparison

variable (Θ : (ModuleCat.extendScalars (algebraMap A A')).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M) ⟶
    (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom).obj
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))).obj M))
  (hΘ : ∀ y : M, Θ.hom (tmulA (1 : A') y) = tmulB (1 : B ⊗[A] A') y)

include hΘ in
/-- An `A'`-linear map out of `A' ⊗[A] M` sending `1 ⊗ m` to `1 ⊗ m` sends `a' ⊗ m` to
`(1 ⊗ a') ⊗ m`. -/
theorem apply_tmulA (a' : A') (y : M) :
    Θ.hom (tmulA a' y) = tmulB (Algebra.TensorProduct.includeRight a' : B ⊗[A] A') y := by
  have key : Θ.hom (a' • tmulA (1 : A') y) = a' • Θ.hom (tmulA (1 : A') y) := map_smul _ _ _
  rw [hΘ y, smul_tmulA, mul_one] at key
  refine key.trans ?_
  show (Algebra.TensorProduct.includeRight a' : B ⊗[A] A') • tmulB (1 : B ⊗[A] A') y = _
  rw [smul_tmulB, mul_one]

include hΘ in
/-- `tensorCancel` is a left inverse of such a map. -/
theorem tensorCancel_apply (u : (ModuleCat.extendScalars (algebraMap A A')).obj
    ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :
    tensorCancel (M := M) (Θ.hom u) = u := by
  refine addMonoidHom_apply_eq_self_of_tmul
    ((tensorCancel (M := M)).comp Θ.hom.toAddMonoidHom) (fun x n => ?_) u
  change tensorCancel (M := M) (Θ.hom (tmulA (ofRestrictScalarsSelf (algebraMap A A') x)
    (ofRestrictScalars (algebraMap A B) n))) = _
  rw [apply_tmulA Θ hΘ, tensorCancel_tmulB_includeRight]
  rfl

include hΘ in
/-- `tensorCancel` is a right inverse of such a map, on pure tensors. -/
theorem apply_tensorCancel_tmulB (w : B ⊗[A] A') (y : M) :
    Θ.hom (tensorCancel (M := M) (tmulB w y)) = tmulB w y := by
  induction w with
  | tmul b a' => rw [tensorCancel_tmulB, apply_tmulA Θ hΘ, ← tmulB_tmul_mul, ← tmulB_smul]
  | add w₁ w₂ h₁ h₂ =>
      rw [tmulB_add_left, map_add, map_add]
      exact congrArg₂ (· + ·) h₁ h₂

include hΘ in
/-- `tensorCancel` is a right inverse of such a map. -/
theorem apply_tensorCancel (z : (ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))).obj M) :
    Θ.hom (tensorCancel (M := M) z) = z :=
  addMonoidHom_apply_eq_self_of_tmul (Θ.hom.toAddMonoidHom.comp (tensorCancel (M := M)))
    (fun w y => apply_tensorCancel_tmulB Θ hΘ w y) z

include hΘ in
/-- **The affine base-change comparison is bijective.**  An `A'`-linear map
`A' ⊗[A] M ⟶ (B ⊗[A] A') ⊗[B] M` carrying `1 ⊗ m` to `1 ⊗ m` is bijective. -/
theorem bijective_of_one_tmul : Function.Bijective Θ.hom :=
  ⟨fun u v huv => by
      rw [← tensorCancel_apply Θ hΘ u, ← tensorCancel_apply Θ hΘ v, huv],
    fun z => ⟨tensorCancel z, apply_tensorCancel Θ hΘ z⟩⟩

end Comparison

end Core


section Geometry

variable (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
  [Algebra A B] [Algebra A A']

/-- The ring square `A → B`, `A → A'`, `B → B ⊗[A] A'`, `A' → B ⊗[A] A'` commutes. -/
theorem specTensor_ring_comm :
    CommRingCat.ofHom (algebraMap A B) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A')) =
      CommRingCat.ofHom (algebraMap A A') ≫
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom := by
  ext a
  show (algebraMap A B a) ⊗ₜ[A] (1 : A') = (1 : B) ⊗ₜ[A] (algebraMap A A' a)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- The square of spectra attached to `A → B`, `A → A'` and `B ⊗[A] A'` commutes. -/
theorem specTensor_square :
    Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A A')) := by
  rw [← Spec.map_comp, ← Spec.map_comp, specTensor_ring_comm]

/-- **The affine case of base change for the direct image**, Stacks Tag 02KG assertion 3, reduced
to global sections: for the square of spectra attached to `A → B` and `A → A'` with upper-left
corner `Spec (B ⊗[A] A')`, the base-change morphism `g^* f_* 𝓕 ⟶ f'_* (g')^* 𝓕` at a
quasi-coherent module `𝓕` on `Spec B` is invertible as soon as it is bijective on global
sections. -/
theorem isIso_baseChangeNatTrans_specTensor_of_bijective
    (F : (Spec (CommRingCat.of B)).Modules) [F.IsQuasicoherent]
    (h : Function.Bijective (moduleSpecΓFunctor.map
      ((AffinePushforward.baseChangeNatTrans (specTensor_square A B A')).app F)).hom) :
    IsIso ((AffinePushforward.baseChangeNatTrans (specTensor_square A B A')).app F) := by
  have h1 : ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F).IsQuasicoherent :=
    AffinePushforward.isQuasicoherent_pushforward_specMap _ F
  have h2 : ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom))).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B)
          (B := A'))))).obj F)).IsQuasicoherent :=
    AffinePushforward.isQuasicoherent_pushforward_specMap _ _
  have h1' : ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⋙
      Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A')))).obj
      F).IsQuasicoherent :=
    SectionsColimit.isQuasicoherent_pullback_specMap _ _
  have h2' : ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A')))) ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom))).obj
      F).IsQuasicoherent := h2
  refine AffineBaseChange.isIso_of_isIso_moduleSpecΓ _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact h

/-- The global-sections comparison of the affine base-change square, as a morphism of
`A'`-modules from `A' ⊗[A] Γ(𝓕, ⊤)` to `(B ⊗[A] A') ⊗[B] Γ(𝓕, ⊤)`.  It is the base-change
morphism on global sections, conjugated by the identifications
`Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso` of the sections of an inverse image
along a morphism of spectra and `Stacks.AlgebraicGeometry.SectionsColimit.pullbackSectionsIso` of
the sections of a direct image. -/
noncomputable def sectionsComparison (F : (Spec (CommRingCat.of B)).Modules)
    [F.IsQuasicoherent]
    (h1 : ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F).IsQuasicoherent) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj
        ((SectionsColimit.sectionsRestrictScalars
          (CommRingCat.ofHom (algebraMap A B))).obj F) ⟶
      (ModuleCat.restrictScalars (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom).hom).obj
        ((ModuleCat.extendScalars (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))).hom).obj
          (moduleSpecΓFunctor.obj F)) :=
  (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A A')).hom).map
      ((SectionsColimit.pullbackSectionsIso (CommRingCat.ofHom (algebraMap A B))).inv.app F) ≫
    (SectionsColimit.sectionsPullbackIso (CommRingCat.ofHom (algebraMap A A'))
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj F)).inv ≫
    moduleSpecΓFunctor.map
      ((AffinePushforward.baseChangeNatTrans (specTensor_square A B A')).app F) ≫
    (SectionsColimit.pullbackSectionsIso (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom)).hom.app
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))))).obj F) ≫
    (ModuleCat.restrictScalars (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A')).toRingHom).hom).map
      (SectionsColimit.sectionsPullbackIso (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A'))) F).hom

end Geometry

end Stacks.AlgebraicGeometry.AffineBaseChangeLocality

end
