module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Crystalline.TwistedBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of a stratified module along a system with products

The quasi-inverse in the proof of [Stacks, Proposition 60.17.4, Tag 07JH] builds a crystal out
of a module `M` over `D` with a *stratification* relative to the levels `T(0)_e` of the system of
[Stacks, Tag 07JN]: an object `A` with a pointing `h : A ⟶ T(0)_e` gets `O(A) ⊗_{D,h} M`, and two
pointings `h, h'` are compared by pulling the stratification back along
`(h, h') : A ⟶ T(1)_e = T(0)_e × T(0)_e`.  This module carries out that descent in the abstract.

## The setting

`Crystalline.StratifiedDescent.System` bundles a category `𝒜` with a functor
`O : 𝒜ᵒᵖ ⥤ CommRingCat`, objects `T0 e`, `T1 e`, `T2 e` with vertices `v e j : T1 e ⟶ T0 e` and
`w e j : T2 e ⟶ T0 e` making `T1 e` and `T2 e` the products of two and three copies of `T0 e`
(stated as bijectivity of composition with the vertices), level maps `lev e : T0 e ⟶ T0 (e+1)`,
structure maps `a e : D →+* O(T0 e)` compatible with the levels, and a pointing of every object.
From the products it defines the pair `System.pair`, the diagonal `System.diag`, the faces
`System.face01`, `System.face12`, `System.face02` and the level map `System.lev1` on `T1`.

A pointing `h : A ⟶ T0 e` has the ring homomorphism `System.ptRing h = O(h) ∘ a e`, and the
twisted tensor products `Crystalline.TwistedScalars (ptRing h) ⊗_D M` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TwistedBaseChange.lean` are the modules
`O(A) ⊗_{D,h} M`.
A change of ring `Crystalline.twistMap ψ`, `b ⊗ m ↦ ψ(b) ⊗ m`, is indexed by a *proof* that `ψ`
carries one structure map to the other, so that no statement below needs a cast.

## The stratification

`Crystalline.StratifiedDescent.Stratification S M` is a family of semilinear maps
`E e : M → TwistedScalars (ptRing (v e 0)) ⊗_D M` over `ptRing (v e 1)` satisfying

* `System.IsUnital`: the pullback of `E e` along the diagonal is `m ↦ 1 ⊗ m`;
* `System.IsCocycle`: on `T2 e`, `c_{p₀₂} = c_{p₀₁} ∘ c_{p₁₂}` for the faces `p_{ij}`, where
  `c_φ = System.comparison` is the base change of the pullback of `E e` along `φ`;
* `System.IsLevelCompatible`: the pullback of `E (e + 1)` along the level map
  `T1 e ⟶ T1 (e + 1)` is `E e`.

Each is stated for all maps with the prescribed vertices, which by the products are exactly the
diagonal, the faces and the level map; `System.isUnital_iff`, `System.isCocycle_iff` and
`System.isLevelCompatible_iff` reduce each to the one map defined from the products.

## The descent

* `Stratification.sections A`: the families over all pointings of `A` compatible under the
  transition maps `Stratification.transition`, an `O(A)`-module;
* `Stratification.evalEquiv h : sections A ≃ₗ[O(A)] TwistedScalars (ptRing h) ⊗_D M`, with
  `Stratification.comparison_evalEquiv` (two pointings at one level differ by the comparison of
  the pair) and `Stratification.evalEquiv_lev` (the pointings `h` and `h ≫ lev e` agree; in the
  form of `Stratification.evalEquivOf_lev` as an equality of maps into one module);
* `Stratification.restrict k`, semilinear over `O(k)`, characterised by
  `Stratification.evalEquiv_restrict`, with `Stratification.restrict_id` and
  `Stratification.restrict_comp`;
* `Stratification.presheaf`, the presheaf of modules over `O`, and
  `Stratification.bijective_semilinearBaseChange_restrict`: the map
  `O(A') ⊗_{O(A)} sections A → sections A'` is bijective, so the presheaf is a crystal;
* `Stratification.presheafMap`, the morphism of presheaves induced by a `D`-linear map commuting
  with the stratifications, with `Stratification.presheafMap_id` and
  `Stratification.presheafMap_comp`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

universe u v₁ u₁ w w' w''

namespace Crystalline

/-! ### Changing the ring of a twisted tensor product -/

section TwistMap

variable {D : Type u} [CommRing D] {M : Type w} [AddCommGroup M] [Module D M]
  {M' : Type w'} [AddCommGroup M'] [Module D M']
  {B : Type w''} {B' : Type w''} {B'' : Type w''} [CommRing B] [CommRing B'] [CommRing B'']

/-- A ring homomorphism `ψ : B →+* B'` carrying `f` to `g` is `D`-linear from the twist of `B`
along `f` to the twist of `B'` along `g`. -/
def twistScalarsHom (ψ : B →+* B') {f : D →+* B} {g : D →+* B'} (h : ψ.comp f = g) :
    TwistedScalars f →ₗ[D] TwistedScalars g where
  toFun b := TwistedScalars.mk g (ψ b.val)
  map_add' x y := map_add ψ x y
  map_smul' d b := by
    change ψ (f d * b.val) = g d * ψ b.val
    rw [map_mul, ← h]
    rfl

/-- **The change of ring of a twisted tensor product**: for `ψ : B →+* B'` carrying `f` to `g`,
the `ψ`-semilinear map `TwistedScalars f ⊗_D M → TwistedScalars g ⊗_D M`, `b ⊗ m ↦ ψ(b) ⊗ m`.
This is the pullback of `M ⊗_{D,f} B` along `ψ`. -/
noncomputable def twistMap (ψ : B →+* B') {f : D →+* B} {g : D →+* B'} (h : ψ.comp f = g) :
    TwistedScalars f ⊗[D] M →ₛₗ[ψ] TwistedScalars g ⊗[D] M where
  toFun := TensorProduct.map (twistScalarsHom ψ h) LinearMap.id
  map_add' := map_add _
  map_smul' b z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
        rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
          TensorProduct.smul_tmul']
        congr 1
        change ψ (b * c.val) = ψ b * ψ c.val
        exact map_mul ψ _ _
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The change of ring on a generator. -/
@[simp] theorem twistMap_tmul (ψ : B →+* B') {f : D →+* B} {g : D →+* B'} (h : ψ.comp f = g)
    (b : TwistedScalars f) (m : M) :
    twistMap ψ h (b ⊗ₜ[D] m) = TwistedScalars.mk g (ψ b.val) ⊗ₜ[D] m := rfl

/-- The change of ring fixes the generators `1 ⊗ m`. -/
@[simp] theorem twistMap_one_tmul (ψ : B →+* B') {f : D →+* B} {g : D →+* B'}
    (h : ψ.comp f = g) (m : M) :
    twistMap ψ h ((1 : TwistedScalars f) ⊗ₜ[D] m) = (1 : TwistedScalars g) ⊗ₜ[D] m := by
  rw [twistMap_tmul, TwistedScalars.val_one, map_one]
  rfl

/-- **The changes of ring compose.** -/
theorem twistMap_twistMap (ψ : B →+* B') (ψ' : B' →+* B'') (ψ'' : B →+* B'')
    (hψ : ψ'.comp ψ = ψ'') {f : D →+* B} {g : D →+* B'} {g' : D →+* B''}
    (h₁ : ψ.comp f = g) (h₂ : ψ'.comp g = g') (h₃ : ψ''.comp f = g')
    (z : TwistedScalars f ⊗[D] M) :
    twistMap ψ' h₂ (twistMap ψ h₁ z) = twistMap ψ'' h₃ z := by
  subst hψ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The change of ring along the identity is the identity. -/
theorem twistMap_eq_self (ψ : B →+* B) (hψ : ψ = RingHom.id B) {f : D →+* B}
    (h : ψ.comp f = f) (z : TwistedScalars f ⊗[D] M) : twistMap ψ h z = z := by
  subst hψ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- **The identification `M ⊗_{D,f} B = M ⊗_{D,g} B` for `f = g`**, the identity on the
generators; it is how two propositionally equal ring homomorphisms are compared without a cast. -/
noncomputable def twistCongr {f g : D →+* B} (h : f = g) :
    TwistedScalars f ⊗[D] M ≃ₗ[B] TwistedScalars g ⊗[D] M :=
  LinearEquiv.ofLinearMap (twistMap (RingHom.id B) (by rw [h]; rfl))
    (twistMap (RingHom.id B) (by rw [h]; rfl))
    (LinearMap.ext fun z ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, twistMap_twistMap _ _ (RingHom.id B) rfl _ _
        (by rfl), twistMap_eq_self _ rfl])
    (LinearMap.ext fun z ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, twistMap_twistMap _ _ (RingHom.id B) rfl _ _
        (by rfl), twistMap_eq_self _ rfl])

/-- The identification `twistCongr` on a generator. -/
@[simp] theorem twistCongr_tmul {f g : D →+* B} (h : f = g) (b : TwistedScalars f) (m : M) :
    twistCongr h (b ⊗ₜ[D] m) = TwistedScalars.mk g b.val ⊗ₜ[D] m := rfl

/-- The identification `twistCongr` fixes the generators `1 ⊗ m`. -/
@[simp] theorem twistCongr_one_tmul {f g : D →+* B} (h : f = g) (m : M) :
    twistCongr h ((1 : TwistedScalars f) ⊗ₜ[D] m) = (1 : TwistedScalars g) ⊗ₜ[D] m := rfl

/-- The identifications `twistCongr` compose. -/
@[simp] theorem twistCongr_twistCongr {f g g' : D →+* B} (h : f = g) (h' : g = g')
    (z : TwistedScalars f ⊗[D] M) : twistCongr h' (twistCongr h z) = twistCongr (h.trans h') z :=
  twistMap_twistMap _ _ (RingHom.id B) rfl _ _ _ z

/-- The identification `twistCongr` along `rfl` is the identity. -/
@[simp] theorem twistCongr_rfl {f : D →+* B} (z : TwistedScalars f ⊗[D] M) :
    twistCongr (rfl : f = f) z = z :=
  twistMap_eq_self _ rfl _ z

/-- **The base change commutes with a change of ring**: if `T'` is `T` followed by the change of
ring along `ψ`, then the base change of `T'` is the base change of `T` read through `ψ`. -/
theorem semilinearBaseChange_twistMap (ψ : B →+* B') {f g : D →+* B} {f' g' : D →+* B'}
    (hf : ψ.comp f = f') (hg : ψ.comp g = g') (T : M →ₛₗ[f] TwistedScalars g ⊗[D] M')
    (T' : M →ₛₗ[f'] TwistedScalars g' ⊗[D] M') (hT : ∀ m, T' m = twistMap ψ hg (T m))
    (z : TwistedScalars f ⊗[D] M) :
    semilinearBaseChange T' (twistMap ψ hf z) = twistMap ψ hg (semilinearBaseChange T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
      rw [twistMap_tmul, semilinearBaseChange_tmul, semilinearBaseChange_tmul, hT,
        map_smulₛₗ]
      rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- `LinearMap.lTensor` on a twisted tensor product, as a `B`-linear map. -/
noncomputable def twistLTensor (f : D →+* B) (φ : M →ₗ[D] M') :
    TwistedScalars f ⊗[D] M →ₗ[B] TwistedScalars f ⊗[D] M' where
  toFun := LinearMap.lTensor (TwistedScalars f) φ
  map_add' := map_add _
  map_smul' b z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => rfl
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `twistLTensor` is `LinearMap.lTensor`. -/
@[simp] theorem twistLTensor_apply (f : D →+* B) (φ : M →ₗ[D] M')
    (z : TwistedScalars f ⊗[D] M) :
    twistLTensor f φ z = LinearMap.lTensor (TwistedScalars f) φ z := rfl

/-- The change of ring commutes with `LinearMap.lTensor`. -/
theorem twistMap_lTensor (ψ : B →+* B') {f : D →+* B} {g : D →+* B'} (h : ψ.comp f = g)
    (φ : M →ₗ[D] M') (z : TwistedScalars f ⊗[D] M) :
    twistMap ψ h (LinearMap.lTensor (TwistedScalars f) φ z) =
      LinearMap.lTensor (TwistedScalars g) φ (twistMap ψ h z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- `1 ⊗ (d • m) = f(d) • (1 ⊗ m)` in the twisted tensor product. -/
@[sga "3 VIIA 4.1.4" "special case"]
theorem one_tmul_smul (f : D →+* B) (d : D) (m : M) :
    (1 : TwistedScalars f) ⊗ₜ[D] (d • m) = f d • ((1 : TwistedScalars f) ⊗ₜ[D] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  rfl

/-- The inverse of the base change of the change of ring,
`b ⊗ m ↦ b ⊗ (1 ⊗ m)`. -/
noncomputable def twistMapInv (ψ : B →+* B') (f : D →+* B) (g : D →+* B') (h : ψ.comp f = g) :
    TwistedScalars g ⊗[D] M →+ TwistedScalars ψ ⊗[B] (TwistedScalars f ⊗[D] M) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b : TwistedScalars g ↦
      AddMonoidHom.mk' (fun m : M ↦
        TwistedScalars.mk ψ b.val ⊗ₜ[B] ((1 : TwistedScalars f) ⊗ₜ[D] m))
        (fun m m' ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]))
      (fun b b' ↦ by
        ext m
        change TwistedScalars.mk ψ (b.val + b'.val) ⊗ₜ[B] _ = _
        exact TensorProduct.add_tmul _ _ _))
    (fun d b m ↦ by
      change TwistedScalars.mk ψ (g d * b.val) ⊗ₜ[B] ((1 : TwistedScalars f) ⊗ₜ[D] m) =
        TwistedScalars.mk ψ b.val ⊗ₜ[B] ((1 : TwistedScalars f) ⊗ₜ[D] (d • m))
      rw [one_tmul_smul, ← TensorProduct.smul_tmul, ← h]
      rfl)

/-- `twistMapInv` on a generator. -/
theorem twistMapInv_tmul (ψ : B →+* B') (f : D →+* B) (g : D →+* B') (h : ψ.comp f = g)
    (b : TwistedScalars g) (m : M) :
    twistMapInv ψ f g h (b ⊗ₜ[D] m) =
      TwistedScalars.mk ψ b.val ⊗ₜ[B] ((1 : TwistedScalars f) ⊗ₜ[D] m) := rfl

/-- **The base change of the change of ring is bijective**:
`B' ⊗_B (TwistedScalars f ⊗_D M) → TwistedScalars g ⊗_D M`, `b' ⊗ x ↦ b' · ψ_* x`, is an
isomorphism for `g = ψ ∘ f`; this is `B' ⊗_B (B ⊗_D M) = B' ⊗_D M`. -/
theorem bijective_semilinearBaseChange_twistMap (ψ : B →+* B') {f : D →+* B} {g : D →+* B'}
    (h : ψ.comp f = g) :
    Function.Bijective (semilinearBaseChange (twistMap (M := M) ψ h)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨twistMapInv ψ f g h, fun t ↦ ?_, fun x ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b m =>
            rw [semilinearBaseChange_tmul, twistMap_tmul, TensorProduct.smul_tmul',
              twistMapInv_tmul, tmul_eq_smul_one_tmul b m, ← TensorProduct.smul_tmul]
            congr 1
            show TwistedScalars.mk ψ (c.val * ψ b.val) = TwistedScalars.mk ψ (ψ b.val * c.val)
            rw [mul_comm]
        | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
        rw [twistMapInv_tmul, semilinearBaseChange_tmul, twistMap_one_tmul,
          tmul_eq_smul_one_tmul b m]
        rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end TwistMap
namespace StratifiedDescent

/-! ### The system -/

/-- **The data of the descent**: objects `T0 e`, `T1 e`, `T2 e` of a category `𝒜` indexed by a
level `e`, with `T1 e` a product of two copies and `T2 e` a product of three copies of `T0 e`
(expressed by the bijectivity of composition with the vertices `v` and `w`), level maps
`lev e : T0 e ⟶ T0 (e + 1)`, a ring homomorphism `a e : D →+* O(T0 e)` compatible with the levels,
and at least one pointing `A ⟶ T0 e` of every object.  This is the shape of the system of
[Stacks, Tag 07JN] used in [Stacks, Tag 07JH]. -/
structure System (𝒜 : Type u₁) [Category.{v₁} 𝒜] (O : 𝒜ᵒᵖ ⥤ CommRingCat.{u}) (D : Type u)
    [CommRing D] where
  /-- The objects `T(0)_e`. -/
  T0 : ℕ → 𝒜
  /-- The objects `T(1)_e`, products of two copies of `T(0)_e`. -/
  T1 : ℕ → 𝒜
  /-- The objects `T(2)_e`, products of three copies of `T(0)_e`. -/
  T2 : ℕ → 𝒜
  /-- The two vertices `T(1)_e ⟶ T(0)_e`. -/
  v : ∀ e, Fin 2 → (T1 e ⟶ T0 e)
  /-- The three vertices `T(2)_e ⟶ T(0)_e`. -/
  w : ∀ e, Fin 3 → (T2 e ⟶ T0 e)
  /-- `T(1)_e` is the product of two copies of `T(0)_e` with projections `v e`. -/
  bijective_v : ∀ (A : 𝒜) (e : ℕ), Function.Bijective (fun h : A ⟶ T1 e ↦ fun j ↦ h ≫ v e j)
  /-- `T(2)_e` is the product of three copies of `T(0)_e` with projections `w e`. -/
  bijective_w : ∀ (A : 𝒜) (e : ℕ), Function.Bijective (fun h : A ⟶ T2 e ↦ fun j ↦ h ≫ w e j)
  /-- The level maps. -/
  lev : ∀ e, T0 e ⟶ T0 (e + 1)
  /-- The structure maps `D → O(T(0)_e)`. -/
  a : ∀ e, D →+* O.obj (op (T0 e))
  /-- The structure maps are compatible with the level maps. -/
  a_lev : ∀ e, (O.map (lev e).op).hom.comp (a (e + 1)) = a e
  /-- Every object has a pointing at some level. -/
  exists_pointing : ∀ A : 𝒜, ∃ e, Nonempty (A ⟶ T0 e)

namespace System

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {O : 𝒜ᵒᵖ ⥤ CommRingCat.{u}} {D : Type u} [CommRing D]
  (S : System 𝒜 O D)

/-! #### The ring homomorphism of a pointing -/

/-- The ring homomorphism `D → O(A)` of a pointing `h : A ⟶ T(0)_e`. -/
def ptRing {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) : D →+* O.obj (op A) :=
  (O.map h.op).hom.comp (S.a e)

/-- The ring homomorphism of a composite pointing. -/
theorem ptRing_comp {A A' : 𝒜} {e : ℕ} (k : A' ⟶ A) (h : A ⟶ S.T0 e) :
    S.ptRing (k ≫ h) = (O.map k.op).hom.comp (S.ptRing h) := by
  simp only [ptRing, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_assoc]

/-- The ring homomorphism of the identity pointing is the structure map. -/
@[simp] theorem ptRing_id (e : ℕ) : S.ptRing (𝟙 (S.T0 e)) = S.a e := by
  rw [ptRing, op_id, O.map_id]
  rfl

/-- **Pulling back the ring homomorphism of a pointing**: if `χ ≫ g = h` then `O(χ) ∘ g = h`
on the ring homomorphisms of the pointings. -/
theorem map_comp_ptRing {A X : 𝒜} {e : ℕ} {χ : A ⟶ X} {g : X ⟶ S.T0 e} {h : A ⟶ S.T0 e}
    (hχ : χ ≫ g = h) : (O.map χ.op).hom.comp (S.ptRing g) = S.ptRing h := by
  rw [← S.ptRing_comp, hχ]

/-- The ring homomorphism of a pointing does not change under a level map. -/
theorem ptRing_lev {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) : S.ptRing (h ≫ S.lev e) = S.ptRing h := by
  rw [S.ptRing_comp, ptRing, S.a_lev]
  rfl

/-- The composite level map `T(0)_e ⟶ T(0)_n` for `e ≤ n`. -/
def levTo (e n : ℕ) (hn : e ≤ n) : S.T0 e ⟶ S.T0 n := Functor.OfSequence.map S.lev e n hn

/-- The composite level map from a level to itself is the identity. -/
@[simp] theorem levTo_self (e : ℕ) (hn : e ≤ e) : S.levTo e e hn = 𝟙 _ :=
  Functor.OfSequence.map_id S.lev e

/-- The composite level map to `n + 1` ends with the level map `lev n`. -/
theorem levTo_succ (e n : ℕ) (hn : e ≤ n) (hn' : e ≤ n + 1) :
    S.levTo e (n + 1) hn' = S.levTo e n hn ≫ S.lev n := by
  rw [levTo, Functor.OfSequence.map_comp S.lev e n (n + 1) hn (Nat.le_succ n),
    Functor.OfSequence.map_le_succ]
  rfl

/-- The composite level maps compose. -/
theorem levTo_trans (e n n' : ℕ) (hn : e ≤ n) (hn' : n ≤ n') (h : e ≤ n') :
    S.levTo e n' h = S.levTo e n hn ≫ S.levTo n n' hn' :=
  Functor.OfSequence.map_comp S.lev e n n' hn hn'

/-- The composite level map from `e` to `e + 1` is `lev e`. -/
theorem levTo_lev (e : ℕ) (h : e ≤ e + 1) : S.levTo e (e + 1) h = S.lev e := by
  rw [S.levTo_succ e e le_rfl, levTo_self, Category.id_comp]

/-- The ring homomorphism of a pointing does not change under a composite level map. -/
theorem ptRing_levTo {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (n : ℕ) (hn : e ≤ n) :
    S.ptRing (h ≫ S.levTo e n hn) = S.ptRing h := by
  induction n, hn using Nat.le_induction with
  | base => rw [levTo_self, Category.comp_id]
  | succ n hen ih =>
      rw [S.levTo_succ e n hen, ← Category.assoc, ptRing_lev, ih]

/-- `map_comp_ptRing` up to a composite level map. -/
theorem map_comp_ptRing_levTo {A X : 𝒜} {e n : ℕ} {χ : A ⟶ X} {g : X ⟶ S.T0 n}
    {h : A ⟶ S.T0 e} (hn : e ≤ n) (hχ : χ ≫ g = h ≫ S.levTo e n hn) :
    (O.map χ.op).hom.comp (S.ptRing g) = S.ptRing h := by
  rw [S.map_comp_ptRing hχ, ptRing_levTo]

/-! #### Pairs and triples -/

/-- The map `A ⟶ T(1)_e` with vertices `h₀` and `h₁`. -/
noncomputable def pair {A : 𝒜} {e : ℕ} (h₀ h₁ : A ⟶ S.T0 e) : A ⟶ S.T1 e :=
  (Equiv.ofBijective _ (S.bijective_v A e)).symm ![h₀, h₁]

/-- The vertices of a pair. -/
theorem pair_v {A : 𝒜} {e : ℕ} (h₀ h₁ : A ⟶ S.T0 e) (j : Fin 2) :
    S.pair h₀ h₁ ≫ S.v e j = ![h₀, h₁] j :=
  congrFun ((Equiv.ofBijective _ (S.bijective_v A e)).apply_symm_apply ![h₀, h₁]) j

/-- The vertex `0` of a pair. -/
@[reassoc (attr := simp)] theorem pair_v_zero {A : 𝒜} {e : ℕ} (h₀ h₁ : A ⟶ S.T0 e) :
    S.pair h₀ h₁ ≫ S.v e 0 = h₀ :=
  S.pair_v h₀ h₁ 0

/-- The vertex `1` of a pair. -/
@[reassoc (attr := simp)] theorem pair_v_one {A : 𝒜} {e : ℕ} (h₀ h₁ : A ⟶ S.T0 e) :
    S.pair h₀ h₁ ≫ S.v e 1 = h₁ :=
  S.pair_v h₀ h₁ 1

/-- Maps into `T(1)_e` are determined by their two vertices. -/
theorem hom_ext_T1 {A : 𝒜} {e : ℕ} {φ ψ : A ⟶ S.T1 e} (h₀ : φ ≫ S.v e 0 = ψ ≫ S.v e 0)
    (h₁ : φ ≫ S.v e 1 = ψ ≫ S.v e 1) : φ = ψ :=
  (S.bijective_v A e).1 (funext fun j ↦ by fin_cases j <;> assumption)

/-- A map into `T(1)_e` is the pair of its vertices. -/
theorem eq_pair {A : 𝒜} {e : ℕ} {φ : A ⟶ S.T1 e} {h₀ h₁ : A ⟶ S.T0 e}
    (h0 : φ ≫ S.v e 0 = h₀) (h1 : φ ≫ S.v e 1 = h₁) : φ = S.pair h₀ h₁ :=
  S.hom_ext_T1 (by rw [h0, pair_v_zero]) (by rw [h1, pair_v_one])

/-- The map `A ⟶ T(2)_e` with vertices `h₀`, `h₁` and `h₂`. -/
noncomputable def triple {A : 𝒜} {e : ℕ} (h₀ h₁ h₂ : A ⟶ S.T0 e) : A ⟶ S.T2 e :=
  (Equiv.ofBijective _ (S.bijective_w A e)).symm ![h₀, h₁, h₂]

/-- The vertices of a triple. -/
theorem triple_w {A : 𝒜} {e : ℕ} (h₀ h₁ h₂ : A ⟶ S.T0 e) (j : Fin 3) :
    S.triple h₀ h₁ h₂ ≫ S.w e j = ![h₀, h₁, h₂] j :=
  congrFun ((Equiv.ofBijective _ (S.bijective_w A e)).apply_symm_apply ![h₀, h₁, h₂]) j

/-- The vertex `0` of a triple. -/
@[reassoc (attr := simp)] theorem triple_w_zero {A : 𝒜} {e : ℕ} (h₀ h₁ h₂ : A ⟶ S.T0 e) :
    S.triple h₀ h₁ h₂ ≫ S.w e 0 = h₀ :=
  S.triple_w h₀ h₁ h₂ 0

/-- The vertex `1` of a triple. -/
@[reassoc (attr := simp)] theorem triple_w_one {A : 𝒜} {e : ℕ} (h₀ h₁ h₂ : A ⟶ S.T0 e) :
    S.triple h₀ h₁ h₂ ≫ S.w e 1 = h₁ :=
  S.triple_w h₀ h₁ h₂ 1

/-- The vertex `2` of a triple. -/
@[reassoc (attr := simp)] theorem triple_w_two {A : 𝒜} {e : ℕ} (h₀ h₁ h₂ : A ⟶ S.T0 e) :
    S.triple h₀ h₁ h₂ ≫ S.w e 2 = h₂ :=
  S.triple_w h₀ h₁ h₂ 2

/-- The diagonal `T(0)_e ⟶ T(1)_e`. -/
noncomputable def diag (e : ℕ) : S.T0 e ⟶ S.T1 e := S.pair (𝟙 _) (𝟙 _)

/-- The face `T(2)_e ⟶ T(1)_e` with vertices `0, 1`. -/
noncomputable def face01 (e : ℕ) : S.T2 e ⟶ S.T1 e := S.pair (S.w e 0) (S.w e 1)

/-- The face `T(2)_e ⟶ T(1)_e` with vertices `1, 2`. -/
noncomputable def face12 (e : ℕ) : S.T2 e ⟶ S.T1 e := S.pair (S.w e 1) (S.w e 2)

/-- The face `T(2)_e ⟶ T(1)_e` with vertices `0, 2`. -/
noncomputable def face02 (e : ℕ) : S.T2 e ⟶ S.T1 e := S.pair (S.w e 0) (S.w e 2)

/-- The level map `T(1)_e ⟶ T(1)_{e+1}`. -/
noncomputable def lev1 (e : ℕ) : S.T1 e ⟶ S.T1 (e + 1) :=
  S.pair (S.v e 0 ≫ S.lev e) (S.v e 1 ≫ S.lev e)

/-- Both vertices of the diagonal are the identity. -/
@[reassoc (attr := simp)] theorem diag_v (e : ℕ) (j : Fin 2) : S.diag e ≫ S.v e j = 𝟙 _ := by
  fin_cases j <;> simp [diag]

/-- The vertex `0` of the face `p₀₁`. -/
@[reassoc (attr := simp)] theorem face01_v_zero (e : ℕ) : S.face01 e ≫ S.v e 0 = S.w e 0 :=
  S.pair_v_zero _ _

/-- The vertex `1` of the face `p₀₁`. -/
@[reassoc (attr := simp)] theorem face01_v_one (e : ℕ) : S.face01 e ≫ S.v e 1 = S.w e 1 :=
  S.pair_v_one _ _

/-- The vertex `0` of the face `p₁₂`. -/
@[reassoc (attr := simp)] theorem face12_v_zero (e : ℕ) : S.face12 e ≫ S.v e 0 = S.w e 1 :=
  S.pair_v_zero _ _

/-- The vertex `1` of the face `p₁₂`. -/
@[reassoc (attr := simp)] theorem face12_v_one (e : ℕ) : S.face12 e ≫ S.v e 1 = S.w e 2 :=
  S.pair_v_one _ _

/-- The vertex `0` of the face `p₀₂`. -/
@[reassoc (attr := simp)] theorem face02_v_zero (e : ℕ) : S.face02 e ≫ S.v e 0 = S.w e 0 :=
  S.pair_v_zero _ _

/-- The vertex `1` of the face `p₀₂`. -/
@[reassoc (attr := simp)] theorem face02_v_one (e : ℕ) : S.face02 e ≫ S.v e 1 = S.w e 2 :=
  S.pair_v_one _ _

/-- The vertices of the level map `T(1)_e ⟶ T(1)_{e+1}`. -/
@[reassoc (attr := simp)] theorem lev1_v (e : ℕ) (j : Fin 2) :
    S.lev1 e ≫ S.v (e + 1) j = S.v e j ≫ S.lev e := by
  fin_cases j <;> simp [lev1]

/-! #### Pulling back a stratification -/

variable {M : Type u} [AddCommGroup M] [Module D M]

/-- **The pullback of a stratification along `φ : A ⟶ T(1)_e`**, the `f'`-semilinear map
`M → TwistedScalars f ⊗_D M`, `m ↦ φ^*(E m)`, for ring homomorphisms `f`, `f'` identified with
the pullbacks along `φ` of those of the two vertices.  The ring homomorphisms are parameters, so
that no statement about the pullback needs a cast. -/
noncomputable def pullStrat
    (E : ∀ e, M →ₛₗ[S.ptRing (S.v e 1)] TwistedScalars (S.ptRing (S.v e 0)) ⊗[D] M)
    {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e) (f f' : D →+* O.obj (op A))
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f') :
    M →ₛₗ[f'] TwistedScalars f ⊗[D] M where
  toFun m := twistMap (O.map φ.op).hom hf (E e m)
  map_add' m m' := by rw [map_add, map_add]
  map_smul' d m := by
    subst hf'
    rw [map_smulₛₗ (E e), map_smulₛₗ (twistMap (O.map φ.op).hom hf)]
    rfl

variable (E : ∀ e, M →ₛₗ[S.ptRing (S.v e 1)] TwistedScalars (S.ptRing (S.v e 0)) ⊗[D] M)

/-- The pullback of a stratification is the change of ring of its value. -/
theorem pullStrat_apply {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e) (f f' : D →+* O.obj (op A))
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f') (m : M) :
    S.pullStrat E φ f f' hf hf' m = twistMap (O.map φ.op).hom hf (E e m) := rfl

/-- The pullback depends only on the map, not on how it is written. -/
theorem pullStrat_congr {A : 𝒜} {e : ℕ} {φ φ' : A ⟶ S.T1 e} (hφ : φ = φ')
    (f f' : D →+* O.obj (op A))
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f')
    (hg : (O.map φ'.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hg' : (O.map φ'.op).hom.comp (S.ptRing (S.v e 1)) = f') (m : M) :
    S.pullStrat E φ f f' hf hf' m = S.pullStrat E φ' f f' hg hg' m := by
  subst hφ
  rfl

/-- **The pullback along a composite is the pullback of the pullback.** -/
theorem pullStrat_comp {A A' : 𝒜} {e : ℕ} (k : A' ⟶ A) (φ : A ⟶ S.T1 e)
    (f f' : D →+* O.obj (op A')) (g g' : D →+* O.obj (op A))
    (hf : (O.map (k ≫ φ).op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map (k ≫ φ).op).hom.comp (S.ptRing (S.v e 1)) = f')
    (hg : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = g)
    (hg' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = g')
    (hk : (O.map k.op).hom.comp g = f) (m : M) :
    S.pullStrat E (k ≫ φ) f f' hf hf' m =
      twistMap (O.map k.op).hom hk (S.pullStrat E φ g g' hg hg' m) := by
  rw [pullStrat_apply, pullStrat_apply, twistMap_twistMap _ _ (O.map (k ≫ φ).op).hom]
  simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp]

/-- `System.pullStrat_comp` for a map written as a composite. -/
theorem pullStrat_comp' {A A' : 𝒜} {e : ℕ} (k : A' ⟶ A) (φ : A ⟶ S.T1 e) (φ' : A' ⟶ S.T1 e)
    (hφ : k ≫ φ = φ') (f f' : D →+* O.obj (op A')) (g g' : D →+* O.obj (op A))
    (hf : (O.map φ'.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ'.op).hom.comp (S.ptRing (S.v e 1)) = f')
    (hg : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = g)
    (hg' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = g')
    (hk : (O.map k.op).hom.comp g = f) (m : M) :
    S.pullStrat E φ' f f' hf hf' m =
      twistMap (O.map k.op).hom hk (S.pullStrat E φ g g' hg hg' m) := by
  subst hφ
  exact S.pullStrat_comp E k φ f f' g g' hf hf' hg hg' hk m

/-- **The comparison `c_φ` of a map `φ : A ⟶ T(1)_e`**: the base change of the pulled-back
stratification, the `O(A)`-linear map `TwistedScalars f' ⊗_D M → TwistedScalars f ⊗_D M`,
`b ⊗ m ↦ b · φ^*(E m)`, from the vertex-`1` trivialisation to the vertex-`0` one. -/
noncomputable def comparison {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e) (f f' : D →+* O.obj (op A))
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f') :
    TwistedScalars f' ⊗[D] M →ₗ[O.obj (op A)] TwistedScalars f ⊗[D] M :=
  semilinearBaseChange (S.pullStrat E φ f f' hf hf')

/-- The comparison on the generators `1 ⊗ m` is the pulled-back stratification. -/
@[simp] theorem comparison_one_tmul {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e)
    (f f' : D →+* O.obj (op A)) (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f') (m : M) :
    S.comparison E φ f f' hf hf' ((1 : TwistedScalars f') ⊗ₜ[D] m) =
      S.pullStrat E φ f f' hf hf' m :=
  semilinearBaseChange_one_tmul _ m

/-- **The comparison is natural**: pulling back the comparison of `φ` along `k` gives the
comparison of `k ≫ φ`. -/
theorem comparison_twistMap {A A' : 𝒜} {e : ℕ} (k : A' ⟶ A) (φ : A ⟶ S.T1 e)
    (φ' : A' ⟶ S.T1 e) (hφ : k ≫ φ = φ') (f f' : D →+* O.obj (op A'))
    (g g' : D →+* O.obj (op A))
    (hf : (O.map φ'.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ'.op).hom.comp (S.ptRing (S.v e 1)) = f')
    (hg : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = g)
    (hg' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = g')
    (hk : (O.map k.op).hom.comp g = f) (hk' : (O.map k.op).hom.comp g' = f')
    (z : TwistedScalars g' ⊗[D] M) :
    S.comparison E φ' f f' hf hf' (twistMap (O.map k.op).hom hk' z) =
      twistMap (O.map k.op).hom hk (S.comparison E φ g g' hg hg' z) :=
  semilinearBaseChange_twistMap _ hk' hk _ _
    (fun m ↦ S.pullStrat_comp' E k φ φ' hφ f f' g g' hf hf' hg hg' hk m) z

/-! #### The axioms of a stratification -/

/-- **The unit axiom**: the pullback of the stratification along the diagonal
`T(0)_e ⟶ T(1)_e` is `m ↦ 1 ⊗ m`.  It is stated for every map with both vertices the identity,
that is for the diagonal, whatever way it is written (`System.isUnital_iff` at `System.diag`). -/
def IsUnital : Prop :=
  ∀ (e : ℕ) (φ : S.T0 e ⟶ S.T1 e) (h₀ : φ ≫ S.v e 0 = 𝟙 _) (h₁ : φ ≫ S.v e 1 = 𝟙 _) (m : M),
    S.pullStrat E φ (S.a e) (S.a e) ((S.map_comp_ptRing h₀).trans (S.ptRing_id e))
      ((S.map_comp_ptRing h₁).trans (S.ptRing_id e)) m = (1 : TwistedScalars (S.a e)) ⊗ₜ[D] m

/-- **The cocycle axiom** on `T(2)_e`: for the three faces `p₀₁, p₁₂, p₀₂ : T(2)_e ⟶ T(1)_e`,
`c_{p₀₁} ∘ c_{p₁₂} = c_{p₀₂}` as maps from the vertex-`2` to the vertex-`0` trivialisation.  It
is stated on the generators `1 ⊗ m`, where `c_{p₁₂}` is the pulled-back stratification, which is
equivalent (`System.isCocycle_iff`), and for all maps with the vertices of the faces. -/
def IsCocycle : Prop :=
  ∀ (e : ℕ) (φ₀₁ φ₁₂ φ₀₂ : S.T2 e ⟶ S.T1 e)
    (h₀₁ : φ₀₁ ≫ S.v e 0 = S.w e 0) (h₀₁' : φ₀₁ ≫ S.v e 1 = S.w e 1)
    (h₁₂ : φ₁₂ ≫ S.v e 0 = S.w e 1) (h₁₂' : φ₁₂ ≫ S.v e 1 = S.w e 2)
    (h₀₂ : φ₀₂ ≫ S.v e 0 = S.w e 0) (h₀₂' : φ₀₂ ≫ S.v e 1 = S.w e 2) (m : M),
    S.comparison E φ₀₁ (S.ptRing (S.w e 0)) (S.ptRing (S.w e 1))
        (S.map_comp_ptRing h₀₁) (S.map_comp_ptRing h₀₁')
      (S.pullStrat E φ₁₂ (S.ptRing (S.w e 1)) (S.ptRing (S.w e 2))
        (S.map_comp_ptRing h₁₂) (S.map_comp_ptRing h₁₂') m) =
    S.pullStrat E φ₀₂ (S.ptRing (S.w e 0)) (S.ptRing (S.w e 2))
      (S.map_comp_ptRing h₀₂) (S.map_comp_ptRing h₀₂') m

/-- **The level axiom**: the pullback of the stratification at level `e + 1` along the level map
`T(1)_e ⟶ T(1)_{e+1}` is the stratification at level `e`.  It is stated for every map with the
vertices of the level map, that is for the level map `System.lev1`. -/
def IsLevelCompatible : Prop :=
  ∀ (e : ℕ) (φ : S.T1 e ⟶ S.T1 (e + 1)) (h₀ : φ ≫ S.v (e + 1) 0 = S.v e 0 ≫ S.lev e)
    (h₁ : φ ≫ S.v (e + 1) 1 = S.v e 1 ≫ S.lev e) (m : M),
    S.pullStrat E φ (S.ptRing (S.v e 0)) (S.ptRing (S.v e 1))
      ((S.map_comp_ptRing h₀).trans (S.ptRing_lev _))
      ((S.map_comp_ptRing h₁).trans (S.ptRing_lev _)) m = E e m

/-- The unit axiom needs checking only at the diagonal `System.diag`. -/
theorem isUnital_iff : S.IsUnital E ↔ ∀ (e : ℕ) (m : M),
    S.pullStrat E (S.diag e) (S.a e) (S.a e)
      ((S.map_comp_ptRing (S.diag_v e 0)).trans (S.ptRing_id e))
      ((S.map_comp_ptRing (S.diag_v e 1)).trans (S.ptRing_id e)) m =
      (1 : TwistedScalars (S.a e)) ⊗ₜ[D] m := by
  refine ⟨fun h e m ↦ h e _ (S.diag_v e 0) (S.diag_v e 1) m, fun h e φ h₀ h₁ m ↦ ?_⟩
  obtain rfl : φ = S.diag e := S.hom_ext_T1 (by simp [h₀]) (by simp [h₁])
  exact h e m

/-- The cocycle axiom needs checking only at the faces `System.face01`, `System.face12` and
`System.face02`, and it is the identity `c_{p₀₁} ∘ c_{p₁₂} = c_{p₀₂}` of linear maps. -/
theorem isCocycle_iff : S.IsCocycle E ↔ ∀ e : ℕ,
    (S.comparison E (S.face01 e) (S.ptRing (S.w e 0)) (S.ptRing (S.w e 1))
        (S.map_comp_ptRing (S.face01_v_zero e)) (S.map_comp_ptRing (S.face01_v_one e))).comp
      (S.comparison E (S.face12 e) (S.ptRing (S.w e 1)) (S.ptRing (S.w e 2))
        (S.map_comp_ptRing (S.face12_v_zero e)) (S.map_comp_ptRing (S.face12_v_one e))) =
    S.comparison E (S.face02 e) (S.ptRing (S.w e 0)) (S.ptRing (S.w e 2))
      (S.map_comp_ptRing (S.face02_v_zero e)) (S.map_comp_ptRing (S.face02_v_one e)) := by
  refine ⟨fun h e ↦ baseChange_ext fun m ↦ ?_,
    fun h e φ₀₁ φ₁₂ φ₀₂ h₀₁ h₀₁' h₁₂ h₁₂' h₀₂ h₀₂' m ↦ ?_⟩
  · rw [LinearMap.comp_apply, comparison_one_tmul, comparison_one_tmul]
    exact h e _ _ _ (S.face01_v_zero e) (S.face01_v_one e) (S.face12_v_zero e)
      (S.face12_v_one e) (S.face02_v_zero e) (S.face02_v_one e) m
  · obtain rfl : φ₀₁ = S.face01 e := S.hom_ext_T1 (by simp [h₀₁]) (by simp [h₀₁'])
    obtain rfl : φ₁₂ = S.face12 e := S.hom_ext_T1 (by simp [h₁₂]) (by simp [h₁₂'])
    obtain rfl : φ₀₂ = S.face02 e := S.hom_ext_T1 (by simp [h₀₂]) (by simp [h₀₂'])
    have := LinearMap.congr_fun (h e) ((1 : TwistedScalars (S.ptRing (S.w e 2))) ⊗ₜ[D] m)
    rwa [LinearMap.comp_apply, comparison_one_tmul, comparison_one_tmul] at this

/-- The level axiom needs checking only at the level map `System.lev1`. -/
theorem isLevelCompatible_iff : S.IsLevelCompatible E ↔ ∀ e : ℕ,
    S.pullStrat E (S.lev1 e) (S.ptRing (S.v e 0)) (S.ptRing (S.v e 1))
      ((S.map_comp_ptRing (S.lev1_v e 0)).trans (S.ptRing_lev _))
      ((S.map_comp_ptRing (S.lev1_v e 1)).trans (S.ptRing_lev _)) = E e := by
  refine ⟨fun h e ↦ LinearMap.ext fun m ↦ h e _ (S.lev1_v e 0) (S.lev1_v e 1) m,
    fun h e φ h₀ h₁ m ↦ ?_⟩
  obtain rfl : φ = S.lev1 e := S.hom_ext_T1 (by simp [h₀]) (by simp [h₁])
  exact LinearMap.congr_fun (h e) m

/-- A pointing of an object: a level `e` and a map `A ⟶ T(0)_e`. -/
abbrev Pointing (A : 𝒜) : Type v₁ := Σ e : ℕ, A ⟶ S.T0 e

/-- A pointing of each object, chosen once. -/
noncomputable def point (A : 𝒜) : S.Pointing A :=
  ⟨(S.exists_pointing A).choose, (S.exists_pointing A).choose_spec.some⟩

end System

/-- **A stratification of `M` relative to the system**: for every level `e`, a semilinear map
`E e : M → TwistedScalars (ptRing (v e 0)) ⊗_D M` over `ptRing (v e 1)` — "the pullback of `m`
along the vertex `1`, written in the vertex-`0` trivialisation" — satisfying the unit, cocycle
and level axioms. -/
structure Stratification {𝒜 : Type u₁} [Category.{v₁} 𝒜] {O : 𝒜ᵒᵖ ⥤ CommRingCat.{u}}
    {D : Type u} [CommRing D] (S : System 𝒜 O D) (M : Type u) [AddCommGroup M] [Module D M] where
  /-- The stratification at each level. -/
  str : ∀ e, M →ₛₗ[S.ptRing (S.v e 1)] TwistedScalars (S.ptRing (S.v e 0)) ⊗[D] M
  /-- The unit axiom. -/
  isUnital : S.IsUnital str
  /-- The cocycle axiom. -/
  isCocycle : S.IsCocycle str
  /-- The level axiom. -/
  isLevelCompatible : S.IsLevelCompatible str

namespace Stratification

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {O : 𝒜ᵒᵖ ⥤ CommRingCat.{u}} {D : Type u} [CommRing D]
  {S : System 𝒜 O D} {M : Type u} [AddCommGroup M] [Module D M] (E : Stratification S M)

/-! ### The comparisons of a stratification -/

/-- **The unit axiom at an arbitrary map**: if both vertices of `φ` agree, `c_φ` is the
identity, read through the identification of the two (equal) ring homomorphisms. -/
theorem comparison_eq_twistCongr {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e)
    (hφ : φ ≫ S.v e 0 = φ ≫ S.v e 1) (f f' : D →+* O.obj (op A))
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f') (hff : f' = f)
    (z : TwistedScalars f' ⊗[D] M) :
    S.comparison E.str φ f f' hf hf' z = twistCongr hff z := by
  have key : S.comparison E.str φ f f' hf hf' = (twistCongr hff).toLinearMap := by
    refine baseChange_ext fun m ↦ ?_
    rw [S.comparison_one_tmul, LinearEquiv.coe_coe, twistCongr_one_tmul]
    have hd : (φ ≫ S.v e 0) ≫ S.diag e = φ := S.hom_ext_T1 (by simp) (by simp [hφ])
    have hk : (O.map (φ ≫ S.v e 0).op).hom.comp (S.a e) = f := by
      rw [← hf, ← S.ptRing_id, ← S.ptRing_comp, ← S.ptRing_comp, Category.comp_id]
    rw [S.pullStrat_comp' E.str (φ ≫ S.v e 0) (S.diag e) φ hd f f' (S.a e) (S.a e) hf hf'
      ((S.map_comp_ptRing (S.diag_v e 0)).trans (S.ptRing_id e))
      ((S.map_comp_ptRing (S.diag_v e 1)).trans (S.ptRing_id e)) hk,
      E.isUnital e (S.diag e) (S.diag_v e 0) (S.diag_v e 1) m, twistMap_one_tmul]
  rw [key]
  rfl

/-- **The cocycle axiom at arbitrary maps**: for three maps `φ₀₁, φ₁₂, φ₀₂ : A ⟶ T(1)_e` with
the vertices of a triangle, `c_{φ₀₁} ∘ c_{φ₁₂} = c_{φ₀₂}`. -/
theorem comparison_comparison {A : 𝒜} {e : ℕ} (φ₀₁ φ₁₂ φ₀₂ : A ⟶ S.T1 e)
    (H₁ : φ₀₁ ≫ S.v e 1 = φ₁₂ ≫ S.v e 0) (H₀ : φ₀₁ ≫ S.v e 0 = φ₀₂ ≫ S.v e 0)
    (H₂ : φ₁₂ ≫ S.v e 1 = φ₀₂ ≫ S.v e 1) (f₀ f₁ f₂ : D →+* O.obj (op A))
    (h₀₁ : (O.map φ₀₁.op).hom.comp (S.ptRing (S.v e 0)) = f₀)
    (h₀₁' : (O.map φ₀₁.op).hom.comp (S.ptRing (S.v e 1)) = f₁)
    (h₁₂ : (O.map φ₁₂.op).hom.comp (S.ptRing (S.v e 0)) = f₁)
    (h₁₂' : (O.map φ₁₂.op).hom.comp (S.ptRing (S.v e 1)) = f₂)
    (h₀₂ : (O.map φ₀₂.op).hom.comp (S.ptRing (S.v e 0)) = f₀)
    (h₀₂' : (O.map φ₀₂.op).hom.comp (S.ptRing (S.v e 1)) = f₂) (z : TwistedScalars f₂ ⊗[D] M) :
    S.comparison E.str φ₀₁ f₀ f₁ h₀₁ h₀₁' (S.comparison E.str φ₁₂ f₁ f₂ h₁₂ h₁₂' z) =
      S.comparison E.str φ₀₂ f₀ f₂ h₀₂ h₀₂' z := by
  have key : (S.comparison E.str φ₀₁ f₀ f₁ h₀₁ h₀₁').comp
      (S.comparison E.str φ₁₂ f₁ f₂ h₁₂ h₁₂') = S.comparison E.str φ₀₂ f₀ f₂ h₀₂ h₀₂' := by
    refine baseChange_ext fun m ↦ ?_
    rw [LinearMap.comp_apply, S.comparison_one_tmul, S.comparison_one_tmul]
    set τ := S.triple (φ₀₁ ≫ S.v e 0) (φ₀₁ ≫ S.v e 1) (φ₁₂ ≫ S.v e 1) with hτ
    have t01 : τ ≫ S.face01 e = φ₀₁ := S.hom_ext_T1 (by simp [τ]) (by simp [τ])
    have t12 : τ ≫ S.face12 e = φ₁₂ := S.hom_ext_T1 (by simp [τ, H₁]) (by simp [τ])
    have t02 : τ ≫ S.face02 e = φ₀₂ := S.hom_ext_T1 (by simp [τ, H₀]) (by simp [τ, H₂])
    have k₀ : (O.map τ.op).hom.comp (S.ptRing (S.w e 0)) = f₀ := by
      rw [S.map_comp_ptRing (S.triple_w_zero _ _ _), S.ptRing_comp]
      exact h₀₁
    have k₁ : (O.map τ.op).hom.comp (S.ptRing (S.w e 1)) = f₁ := by
      rw [S.map_comp_ptRing (S.triple_w_one _ _ _), S.ptRing_comp]
      exact h₀₁'
    have k₂ : (O.map τ.op).hom.comp (S.ptRing (S.w e 2)) = f₂ := by
      rw [S.map_comp_ptRing (S.triple_w_two _ _ _), S.ptRing_comp]
      exact h₁₂'
    rw [S.pullStrat_comp' E.str τ (S.face12 e) φ₁₂ t12 f₁ f₂ _ _ h₁₂ h₁₂'
        (S.map_comp_ptRing (S.face12_v_zero e)) (S.map_comp_ptRing (S.face12_v_one e)) k₁,
      S.comparison_twistMap E.str τ (S.face01 e) φ₀₁ t01 f₀ f₁ _ _ h₀₁ h₀₁'
        (S.map_comp_ptRing (S.face01_v_zero e)) (S.map_comp_ptRing (S.face01_v_one e)) k₀ k₁,
      E.isCocycle e _ _ _ (S.face01_v_zero e) (S.face01_v_one e) (S.face12_v_zero e)
        (S.face12_v_one e) (S.face02_v_zero e) (S.face02_v_one e) m]
    exact (S.pullStrat_comp' E.str τ (S.face02 e) φ₀₂ t02 f₀ f₂ _ _ h₀₂ h₀₂'
      (S.map_comp_ptRing (S.face02_v_zero e)) (S.map_comp_ptRing (S.face02_v_one e)) k₀ m).symm
  exact LinearMap.congr_fun key z

/-- **The level axiom at an arbitrary map**: the comparison of a map at level `e + 1` whose
vertices are those of `φ` followed by the level map is the comparison of `φ`. -/
theorem comparison_lev {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e) (φ' : A ⟶ S.T1 (e + 1))
    (H₀ : φ' ≫ S.v (e + 1) 0 = φ ≫ S.v e 0 ≫ S.lev e)
    (H₁ : φ' ≫ S.v (e + 1) 1 = φ ≫ S.v e 1 ≫ S.lev e) (f f' : D →+* O.obj (op A))
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f')
    (hg : (O.map φ'.op).hom.comp (S.ptRing (S.v (e + 1) 0)) = f)
    (hg' : (O.map φ'.op).hom.comp (S.ptRing (S.v (e + 1) 1)) = f') :
    S.comparison E.str φ' f f' hg hg' = S.comparison E.str φ f f' hf hf' := by
  refine baseChange_ext fun m ↦ ?_
  rw [S.comparison_one_tmul, S.comparison_one_tmul,
    S.pullStrat_comp' E.str φ (S.lev1 e) φ' (S.hom_ext_T1 (by simp [H₀]) (by simp [H₁])) f f'
      _ _ hg hg' ((S.map_comp_ptRing (S.lev1_v e 0)).trans (S.ptRing_lev _))
      ((S.map_comp_ptRing (S.lev1_v e 1)).trans (S.ptRing_lev _)) hf,
    E.isLevelCompatible e (S.lev1 e) (S.lev1_v e 0) (S.lev1_v e 1) m]
  rfl

/-- **The comparison does not depend on the level**: the comparison of a map at level `n ≥ e`
whose vertices are those of `φ` followed by the level maps is the comparison of `φ`. -/
theorem comparison_levTo {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e) (f f' : D →+* O.obj (op A))
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v e 1)) = f') (n : ℕ) (hn : e ≤ n)
    (φ' : A ⟶ S.T1 n) (H₀ : φ' ≫ S.v n 0 = φ ≫ S.v e 0 ≫ S.levTo e n hn)
    (H₁ : φ' ≫ S.v n 1 = φ ≫ S.v e 1 ≫ S.levTo e n hn)
    (hg : (O.map φ'.op).hom.comp (S.ptRing (S.v n 0)) = f)
    (hg' : (O.map φ'.op).hom.comp (S.ptRing (S.v n 1)) = f') :
    S.comparison E.str φ' f f' hg hg' = S.comparison E.str φ f f' hf hf' := by
  induction n, hn using Nat.le_induction with
  | base =>
      obtain rfl : φ' = φ := S.hom_ext_T1 (by simpa using H₀) (by simpa using H₁)
      rfl
  | succ n hen ih =>
      have hψ₀ : (O.map (S.pair (φ ≫ S.v e 0 ≫ S.levTo e n hen)
          (φ ≫ S.v e 1 ≫ S.levTo e n hen)).op).hom.comp (S.ptRing (S.v n 0)) = f := by
        rw [S.map_comp_ptRing (S.pair_v_zero _ _), ← Category.assoc, S.ptRing_levTo,
          S.ptRing_comp]
        exact hf
      have hψ₁ : (O.map (S.pair (φ ≫ S.v e 0 ≫ S.levTo e n hen)
          (φ ≫ S.v e 1 ≫ S.levTo e n hen)).op).hom.comp (S.ptRing (S.v n 1)) = f' := by
        rw [S.map_comp_ptRing (S.pair_v_one _ _), ← Category.assoc, S.ptRing_levTo,
          S.ptRing_comp]
        exact hf'
      rw [← ih _ (S.pair_v_zero _ _) (S.pair_v_one _ _) hψ₀ hψ₁]
      exact E.comparison_lev _ φ' (by rw [H₀, S.levTo_succ e n hen]; simp)
        (by rw [H₁, S.levTo_succ e n hen]; simp) f f' hψ₀ hψ₁ hg hg'

/-! ### The transition maps between pointings -/

/-- **The transition map between two pointings** `h : A ⟶ T(0)_e` and `h' : A ⟶ T(0)_{e'}`: the
comparison of the pair `(h, h')`, taken at the level `max e e'`.  By
`Crystalline.StratifiedDescent.Stratification.comparison_eq_transition` it is the comparison of
any map with these vertices at any common level. -/
noncomputable def transition {A : 𝒜} {e e' : ℕ} (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e') :
    TwistedScalars (S.ptRing h') ⊗[D] M →ₗ[O.obj (op A)] TwistedScalars (S.ptRing h) ⊗[D] M :=
  S.comparison E.str (S.pair (h ≫ S.levTo e (max e e') (le_max_left _ _))
      (h' ≫ S.levTo e' (max e e') (le_max_right _ _))) _ _
    (S.map_comp_ptRing_levTo _ (S.pair_v_zero _ _)) (S.map_comp_ptRing_levTo _ (S.pair_v_one _ _))

/-- The comparison of the pair of `h` and `h'` pushed to any common level `n` is the transition
map. -/
private theorem comparison_pair_levTo {A : 𝒜} {e e' : ℕ} (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e')
    (n : ℕ) (hn : e ≤ n) (hn' : e' ≤ n) :
    S.comparison E.str (S.pair (h ≫ S.levTo e n hn) (h' ≫ S.levTo e' n hn')) _ _
      (S.map_comp_ptRing_levTo hn (S.pair_v_zero _ _))
      (S.map_comp_ptRing_levTo hn' (S.pair_v_one _ _)) = E.transition h h' :=
  E.comparison_levTo _ _ _ _ _ n (max_le hn hn') _
    (by rw [S.pair_v_zero, S.pair_v_zero_assoc, Category.assoc,
      ← S.levTo_trans e _ _ (le_max_left _ _) (max_le hn hn') hn])
    (by rw [S.pair_v_one, S.pair_v_one_assoc, Category.assoc,
      ← S.levTo_trans e' _ _ (le_max_right _ _) (max_le hn hn') hn']) _ _

/-- **The comparison of any map with vertices `h` and `h'` at any common level is the transition
map.** -/
theorem comparison_eq_transition {A : 𝒜} {e e' : ℕ} (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e')
    (n : ℕ) (hn : e ≤ n) (hn' : e' ≤ n) (φ : A ⟶ S.T1 n)
    (H₀ : φ ≫ S.v n 0 = h ≫ S.levTo e n hn) (H₁ : φ ≫ S.v n 1 = h' ≫ S.levTo e' n hn')
    (hf : (O.map φ.op).hom.comp (S.ptRing (S.v n 0)) = S.ptRing h)
    (hf' : (O.map φ.op).hom.comp (S.ptRing (S.v n 1)) = S.ptRing h') :
    S.comparison E.str φ _ _ hf hf' = E.transition h h' := by
  have hN : n ≤ max n (max e e') := le_max_left _ _
  rw [← E.comparison_pair_levTo h h' _ (hn.trans hN) (hn'.trans hN)]
  exact (E.comparison_levTo φ _ _ hf hf' _ hN _
    (by rw [S.pair_v_zero, ← Category.assoc, H₀, Category.assoc,
      ← S.levTo_trans e n _ hn hN (hn.trans hN)])
    (by rw [S.pair_v_one, ← Category.assoc, H₁, Category.assoc,
      ← S.levTo_trans e' n _ hn' hN (hn'.trans hN)]) _ _).symm

/-- **The transition map from a pointing to itself is the identity.** -/
@[simp] theorem transition_self {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e)
    (z : TwistedScalars (S.ptRing h) ⊗[D] M) : E.transition h h z = z := by
  rw [transition, E.comparison_eq_twistCongr _ (by simp) _ _ _ _ rfl]
  exact twistMap_eq_self _ rfl _ z

/-- **The transition maps compose**: the cocycle condition between pointings at arbitrary
levels. -/
theorem transition_transition {A : 𝒜} {e e' e'' : ℕ} (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e')
    (h'' : A ⟶ S.T0 e'') (z : TwistedScalars (S.ptRing h'') ⊗[D] M) :
    E.transition h h' (E.transition h' h'' z) = E.transition h h'' z := by
  set n := max (max e e') e''
  have h₀ : e ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have h₁ : e' ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have h₂ : e'' ≤ n := le_max_right _ _
  rw [← E.comparison_pair_levTo h h' n h₀ h₁, ← E.comparison_pair_levTo h' h'' n h₁ h₂,
    ← E.comparison_pair_levTo h h'' n h₀ h₂]
  exact E.comparison_comparison _ _ _ (by simp) (by simp) (by simp) _ _ _ _ _ _ _ _ _ z

/-- **The transition maps are natural**: pulling back the transition map between `h` and `h'`
along `k` gives the transition map between `k ≫ h` and `k ≫ h'`. -/
theorem transition_twistMap {A A' : 𝒜} {e e' : ℕ} (k : A' ⟶ A) (h : A ⟶ S.T0 e)
    (h' : A ⟶ S.T0 e') (z : TwistedScalars (S.ptRing h') ⊗[D] M) :
    E.transition (k ≫ h) (k ≫ h') (twistMap (O.map k.op).hom (S.ptRing_comp k h').symm z) =
      twistMap (O.map k.op).hom (S.ptRing_comp k h).symm (E.transition h h' z) := by
  have hf := S.map_comp_ptRing_levTo (A := A') (χ := k ≫ S.pair
    (h ≫ S.levTo e (max e e') (le_max_left _ _)) (h' ≫ S.levTo e' (max e e') (le_max_right _ _)))
    (g := S.v _ 0) (h := k ≫ h) (le_max_left _ _) (by simp)
  have hf' := S.map_comp_ptRing_levTo (A := A') (χ := k ≫ S.pair
    (h ≫ S.levTo e (max e e') (le_max_left _ _)) (h' ≫ S.levTo e' (max e e') (le_max_right _ _)))
    (g := S.v _ 1) (h := k ≫ h') (le_max_right _ _) (by simp)
  rw [← E.comparison_eq_transition (k ≫ h) (k ≫ h') (max e e') (le_max_left _ _)
    (le_max_right _ _) _ (by simp) (by simp) hf hf']
  exact S.comparison_twistMap E.str k _ _ rfl _ _ _ _ hf hf' _ _ _ _ z

/-! ### The descended module -/

/-- **The descended module over `A`**: the families `(z_h)` over all pointings `h` of `A`, with
`z_h ∈ TwistedScalars (ptRing h) ⊗_D M`, compatible under the transition maps.  It is an
`O(A)`-submodule of the product. -/
def sectionsSubmodule (A : 𝒜) :
    Submodule (O.obj (op A)) (∀ p : S.Pointing A, TwistedScalars (S.ptRing p.2) ⊗[D] M) where
  carrier := {z | ∀ p q : S.Pointing A, E.transition p.2 q.2 (z q) = z p}
  add_mem' {z z'} hz hz' p q := by
    change E.transition p.2 q.2 (z q + z' q) = z p + z' p
    rw [map_add, hz p q, hz' p q]
  zero_mem' p q := by
    change E.transition p.2 q.2 0 = 0
    rw [map_zero]
  smul_mem' b z hz p q := by
    change E.transition p.2 q.2 (b • z q) = b • z p
    rw [map_smul, hz p q]

/-- The descended module over `A`, an `O(A)`-module. -/
abbrev sections (A : 𝒜) : Type (max u v₁) := ↥(E.sectionsSubmodule A)

/-- **Evaluation at a pointing is an isomorphism** `sections A ≃ TwistedScalars (ptRing h) ⊗_D M`;
the inverse sends `x` to the family `h' ↦ transition h' h x`. -/
noncomputable def evalEquiv {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) :
    E.sections A ≃ₗ[O.obj (op A)] TwistedScalars (S.ptRing h) ⊗[D] M where
  toFun z := z.val ⟨e, h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨fun q ↦ E.transition q.2 h x, fun p q ↦ E.transition_transition p.2 q.2 h x⟩
  left_inv z := Subtype.ext (funext fun q ↦ z.property q ⟨e, h⟩)
  right_inv x := E.transition_self h x

/-- Evaluation at a pointing is the component of the family. -/
theorem evalEquiv_apply {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (z : E.sections A) :
    E.evalEquiv h z = z.val ⟨e, h⟩ := rfl

/-- The inverse of the evaluation at `h`, evaluated at `h'`, is the transition map. -/
@[simp] theorem evalEquiv_symm_apply {A : 𝒜} {e e' : ℕ} (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e')
    (x : TwistedScalars (S.ptRing h) ⊗[D] M) :
    E.evalEquiv h' ((E.evalEquiv h).symm x) = E.transition h' h x := rfl

/-- Two sections agreeing at every pointing are equal. -/
@[ext] theorem sections_ext {A : 𝒜} {z z' : E.sections A}
    (H : ∀ (e : ℕ) (h : A ⟶ S.T0 e), E.evalEquiv h z = E.evalEquiv h z') : z = z' :=
  Subtype.ext (funext fun p ↦ H p.1 p.2)

/-- **The evaluations at two pointings differ by the transition map.** -/
@[simp] theorem transition_evalEquiv {A : 𝒜} {e e' : ℕ} (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e')
    (z : E.sections A) : E.transition h h' (E.evalEquiv h' z) = E.evalEquiv h z :=
  z.property ⟨e, h⟩ ⟨e', h'⟩

/-- **The evaluations at two pointings at the same level differ by the comparison of the
pair**: `evalEquiv h = c_φ ∘ evalEquiv h'` for any `φ : A ⟶ T(1)_e` with vertices `h` and `h'`,
for instance `System.pair h h'`. -/
theorem comparison_evalEquiv {A : 𝒜} {e : ℕ} (φ : A ⟶ S.T1 e) (h h' : A ⟶ S.T0 e)
    (H₀ : φ ≫ S.v e 0 = h) (H₁ : φ ≫ S.v e 1 = h') (z : E.sections A) :
    S.comparison E.str φ (S.ptRing h) (S.ptRing h') (S.map_comp_ptRing H₀)
      (S.map_comp_ptRing H₁) (E.evalEquiv h' z) = E.evalEquiv h z := by
  rw [E.comparison_eq_transition h h' e le_rfl le_rfl φ (by simpa using H₀) (by simpa using H₁)]
  exact E.transition_evalEquiv h h' z

/-- **The evaluations at two pointings that agree after the level maps** are identified by the
identification of the (equal) ring homomorphisms. -/
theorem evalEquiv_eq_twistCongr {A : 𝒜} {e e' : ℕ} (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e')
    (n : ℕ) (hn : e ≤ n) (hn' : e' ≤ n) (H : h ≫ S.levTo e n hn = h' ≫ S.levTo e' n hn')
    (hg : S.ptRing h = S.ptRing h') (z : E.sections A) :
    E.evalEquiv h' z = twistCongr hg (E.evalEquiv h z) := by
  rw [← E.transition_evalEquiv h' h z, ← E.comparison_eq_transition h' h n hn' hn
    (S.pair (h' ≫ S.levTo e' n hn') (h' ≫ S.levTo e' n hn')) (S.pair_v_zero _ _)
    ((S.pair_v_one _ _).trans H.symm) (S.map_comp_ptRing_levTo hn' (S.pair_v_zero _ _))
    (S.map_comp_ptRing_levTo hn ((S.pair_v_one _ _).trans H.symm))]
  exact E.comparison_eq_twistCongr _ (by simp) _ _ _ _ hg _

/-- **The evaluation at `h ≫ lev e` is the evaluation at `h`**, the two twisted tensor products
being identified along the equality `ptRing (h ≫ lev e) = ptRing h` of the structure maps. -/
theorem evalEquiv_lev {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (z : E.sections A) :
    E.evalEquiv (h ≫ S.lev e) z = twistCongr (S.ptRing_lev h).symm (E.evalEquiv h z) :=
  E.evalEquiv_eq_twistCongr h (h ≫ S.lev e) (e + 1) (Nat.le_succ e) le_rfl
    (by rw [S.levTo_lev, S.levTo_self, Category.comp_id]) _ z

/-- The evaluation at `h ≫ levTo e n` is the evaluation at `h`. -/
theorem evalEquiv_levTo {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (n : ℕ) (hn : e ≤ n)
    (z : E.sections A) :
    E.evalEquiv (h ≫ S.levTo e n hn) z = twistCongr (S.ptRing_levTo h n hn).symm
      (E.evalEquiv h z) :=
  E.evalEquiv_eq_twistCongr h _ n hn le_rfl (by rw [S.levTo_self, Category.comp_id]) _ z

/-- **Evaluation at a pointing, into any twisted tensor product along a ring homomorphism equal
to that of the pointing.**  Its point is `Stratification.evalEquivOf_lev`: the evaluations at
`h` and at `h ≫ lev e` are then maps into the same module, and equal. -/
noncomputable def evalEquivOf {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (f : D →+* O.obj (op A))
    (hf : S.ptRing h = f) : E.sections A ≃ₗ[O.obj (op A)] TwistedScalars f ⊗[D] M :=
  (E.evalEquiv h).trans (twistCongr hf)

/-- `evalEquivOf h f hf` is the evaluation at `h` followed by `twistCongr hf`. -/
@[simp] theorem evalEquivOf_apply {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (f : D →+* O.obj (op A))
    (hf : S.ptRing h = f) (z : E.sections A) :
    E.evalEquivOf h f hf z = twistCongr hf (E.evalEquiv h z) := rfl

/-- `evalEquivOf` at the ring homomorphism of the pointing is `evalEquiv`. -/
@[simp] theorem evalEquivOf_rfl {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) :
    E.evalEquivOf h (S.ptRing h) rfl = E.evalEquiv h :=
  LinearEquiv.ext fun _ ↦ twistCongr_rfl _

/-- **The evaluations at `h` and `h ≫ lev e` agree**, as maps into the same module. -/
theorem evalEquivOf_lev {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (f : D →+* O.obj (op A))
    (hf : S.ptRing (h ≫ S.lev e) = f) (hf' : S.ptRing h = f) :
    E.evalEquivOf (h ≫ S.lev e) f hf = E.evalEquivOf h f hf' :=
  LinearEquiv.ext fun z ↦ by rw [evalEquivOf_apply, evalEquiv_lev, twistCongr_twistCongr]; rfl

/-- **The evaluations at `h` and `h ≫ levTo e n` agree**, as maps into the same module. -/
theorem evalEquivOf_levTo {A : 𝒜} {e : ℕ} (h : A ⟶ S.T0 e) (n : ℕ) (hn : e ≤ n)
    (f : D →+* O.obj (op A)) (hf : S.ptRing (h ≫ S.levTo e n hn) = f) (hf' : S.ptRing h = f) :
    E.evalEquivOf (h ≫ S.levTo e n hn) f hf = E.evalEquivOf h f hf' :=
  LinearEquiv.ext fun z ↦ by
    rw [evalEquivOf_apply, evalEquiv_levTo, twistCongr_twistCongr]; rfl

/-! ### The restriction maps -/

/-- **The restriction map** `sections A → sections A'` along `k : A' ⟶ A`, semilinear over
`O(k)`: read through a pointing `h` of `A` and the pointing `k ≫ h` of `A'`, it is
`b ⊗ m ↦ O(k)(b) ⊗ m` (`Crystalline.StratifiedDescent.Stratification.evalEquiv_restrict`). -/
noncomputable def restrict {A A' : 𝒜} (k : A' ⟶ A) :
    E.sections A →ₛₗ[(O.map k.op).hom] E.sections A' where
  toFun z := (E.evalEquiv (k ≫ (S.point A).2)).symm
    (twistMap (O.map k.op).hom (S.ptRing_comp k _).symm (E.evalEquiv (S.point A).2 z))
  map_add' z z' := by rw [map_add, map_add, map_add]
  map_smul' b z := by rw [map_smul, map_smulₛₗ, map_smul]

/-- **The restriction map read through a pointing**: `evalEquiv (k ≫ h) ∘ restrict k` is the
change of ring along `O(k)` composed with `evalEquiv h`. -/
@[simp] theorem evalEquiv_restrict {A A' : 𝒜} {e : ℕ} (k : A' ⟶ A) (h : A ⟶ S.T0 e)
    (z : E.sections A) :
    E.evalEquiv (k ≫ h) (E.restrict k z) =
      twistMap (O.map k.op).hom (S.ptRing_comp k h).symm (E.evalEquiv h z) := by
  show E.transition (k ≫ h) (k ≫ (S.point A).2) (twistMap (O.map k.op).hom _
    (E.evalEquiv (S.point A).2 z)) = _
  rw [E.transition_twistMap, E.transition_evalEquiv]

/-- `evalEquiv_restrict` at a pointing `h'` of `A'` with `k ≫ h = h'`. -/
theorem evalEquiv_restrict' {A A' : 𝒜} {e : ℕ} (k : A' ⟶ A) (h : A ⟶ S.T0 e)
    (h' : A' ⟶ S.T0 e) (hk : k ≫ h = h') (z : E.sections A) :
    E.evalEquiv h' (E.restrict k z) =
      twistMap (O.map k.op).hom (S.map_comp_ptRing hk) (E.evalEquiv h z) := by
  subst hk
  exact E.evalEquiv_restrict k h z

/-- **The restriction along the identity is the identity.** -/
@[simp] theorem restrict_id {A : 𝒜} (z : E.sections A) : E.restrict (𝟙 A) z = z := by
  ext e h
  rw [E.evalEquiv_restrict' (𝟙 A) h h (Category.id_comp h)]
  exact twistMap_eq_self _ (by rw [op_id, O.map_id]; rfl) _ _

/-- **The restriction maps compose.** -/
theorem restrict_comp {A A' A'' : 𝒜} (k' : A'' ⟶ A') (k : A' ⟶ A) (z : E.sections A) :
    E.restrict (k' ≫ k) z = E.restrict k' (E.restrict k z) := by
  refine (E.evalEquiv (k' ≫ k ≫ (S.point A).2)).injective ?_
  rw [E.evalEquiv_restrict' (k' ≫ k) _ _ (Category.assoc _ _ _), E.evalEquiv_restrict,
    E.evalEquiv_restrict, twistMap_twistMap]
  rw [op_comp, O.map_comp]
  rfl

/-- **The descended presheaf of modules** on `𝒜` over the structure presheaf `O`: its value at
`A` is `sections A`, its restriction maps are `restrict`. -/
noncomputable def presheaf : PresheafOfModules.{max u v₁} (O ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of ((O ⋙ forget₂ CommRingCat RingCat).obj X) (E.sections X.unop)
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((O ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
      (ModuleCat.of ((O ⋙ forget₂ CommRingCat RingCat).obj Y) (E.sections Y.unop)))
    { toFun := E.restrict f.unop
      map_add' := map_add _
      map_smul' := map_smulₛₗ (E.restrict f.unop) }
  map_id X := by
    ext z
    exact E.restrict_id z
  map_comp {X Y Z} f g := by
    ext z
    exact E.restrict_comp g.unop f.unop z

/-- The value of the descended presheaf at `A` is `sections A`. -/
@[simp] theorem presheaf_obj (X : 𝒜ᵒᵖ) :
    (E.presheaf.obj X : Type (max u v₁)) = E.sections X.unop :=
  rfl

/-- The restriction maps of the descended presheaf are `restrict`. -/
@[simp] theorem presheaf_map_apply {X Y : 𝒜ᵒᵖ} (f : X ⟶ Y) (z : E.sections X.unop) :
    E.presheaf.map f z = E.restrict f.unop z := rfl

/-! ### The base change property -/

/-- **The descended presheaf is a crystal**: for `k : A' ⟶ A` the map
`O(A') ⊗_{O(A)} sections A → sections A'`, `r ⊗ z ↦ r · restrict k z`, is bijective.  The
source is the twisted tensor product along `O(k)`, which is `O(A') ⊗_{O(A)} sections A` for the
`O(A)`-algebra structure of `O(A')` given by `O(k)`. -/
theorem bijective_semilinearBaseChange_restrict {A A' : 𝒜} (k : A' ⟶ A) :
    Function.Bijective (semilinearBaseChange (E.restrict k)) := by
  set ev := E.evalEquiv (S.point A).2
  set ev' := E.evalEquiv (k ≫ (S.point A).2)
  have key : ⇑(semilinearBaseChange (E.restrict k)) = ev'.symm ∘
      semilinearBaseChange (twistMap (M := M) (O.map k.op).hom (S.ptRing_comp k _).symm) ∘
      TensorProduct.congr (LinearEquiv.refl _ (TwistedScalars (O.map k.op).hom)) ev := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c z =>
        show c.val • E.restrict k z = ev'.symm (c.val • twistMap _ _ (ev z))
        rw [map_smul]
        rfl
    | add x y hx hy =>
        simp only [Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
  rw [key]
  exact ev'.symm.bijective.comp ((bijective_semilinearBaseChange_twistMap _ _).comp
    (TensorProduct.congr _ ev).bijective)

/-! ### Functoriality in the stratified module -/

variable {M' M'' : Type u} [AddCommGroup M'] [Module D M'] [AddCommGroup M''] [Module D M'']
  (E' : Stratification S M') (E'' : Stratification S M'')

/-- A map commuting with the stratifications commutes with their pullbacks. -/
theorem pullStrat_map (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) {A : 𝒜} {e : ℕ}
    (χ : A ⟶ S.T1 e) (f f' : D →+* O.obj (op A))
    (hf : (O.map χ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map χ.op).hom.comp (S.ptRing (S.v e 1)) = f') (m : M) :
    S.pullStrat E'.str χ f f' hf hf' (φ m) =
      LinearMap.lTensor _ φ (S.pullStrat E.str χ f f' hf hf' m) := by
  rw [S.pullStrat_apply, S.pullStrat_apply, hφ, twistMap_lTensor]

/-- A map commuting with the stratifications commutes with the comparisons. -/
theorem comparison_map (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) {A : 𝒜} {e : ℕ}
    (χ : A ⟶ S.T1 e) (f f' : D →+* O.obj (op A))
    (hf : (O.map χ.op).hom.comp (S.ptRing (S.v e 0)) = f)
    (hf' : (O.map χ.op).hom.comp (S.ptRing (S.v e 1)) = f') (z : TwistedScalars f' ⊗[D] M) :
    S.comparison E'.str χ f f' hf hf' (LinearMap.lTensor _ φ z) =
      LinearMap.lTensor _ φ (S.comparison E.str χ f f' hf hf' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
      rw [LinearMap.lTensor_tmul]
      show b.val • S.pullStrat E'.str χ f f' hf hf' (φ m) =
        twistLTensor f φ (b.val • S.pullStrat E.str χ f f' hf hf' m)
      rw [map_smul, E.pullStrat_map E' φ hφ]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- A map commuting with the stratifications commutes with the transition maps. -/
theorem transition_map (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) {A : 𝒜} {e e' : ℕ}
    (h : A ⟶ S.T0 e) (h' : A ⟶ S.T0 e') (z : TwistedScalars (S.ptRing h') ⊗[D] M) :
    E'.transition h h' (LinearMap.lTensor _ φ z) = LinearMap.lTensor _ φ (E.transition h h' z) :=
  E.comparison_map E' φ hφ _ _ _ _ _ z

/-- **The map of descended modules induced by a map commuting with the stratifications**,
`(z_h) ↦ ((1 ⊗ φ) z_h)`. -/
noncomputable def mapSections (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) (A : 𝒜) :
    E.sections A →ₗ[O.obj (op A)] E'.sections A where
  toFun z := ⟨fun p ↦ LinearMap.lTensor _ φ (z.val p), fun p q ↦ by
    change E'.transition p.2 q.2 (LinearMap.lTensor _ φ (z.val q)) = LinearMap.lTensor _ φ (z.val p)
    rw [E.transition_map E' φ hφ, z.property p q]⟩
  map_add' z z' := Subtype.ext (funext fun p ↦ map_add (LinearMap.lTensor _ φ) (z.val p) _)
  map_smul' b z := Subtype.ext (funext fun p ↦ (twistLTensor (S.ptRing p.2) φ).map_smul b (z.val p))

/-- The induced map read through a pointing is `1 ⊗ φ`. -/
@[simp] theorem evalEquiv_mapSections (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) {A : 𝒜} {e : ℕ}
    (h : A ⟶ S.T0 e) (z : E.sections A) :
    E'.evalEquiv h (E.mapSections E' φ hφ A z) = LinearMap.lTensor _ φ (E.evalEquiv h z) := rfl

/-- The induced map commutes with the restriction maps. -/
theorem restrict_mapSections (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) {A A' : 𝒜}
    (k : A' ⟶ A) (z : E.sections A) :
    E'.restrict k (E.mapSections E' φ hφ A z) = E.mapSections E' φ hφ A' (E.restrict k z) := by
  ext e h
  rw [evalEquiv_mapSections, ← E'.transition_evalEquiv h (k ≫ (S.point A).2),
    ← E.transition_evalEquiv h (k ≫ (S.point A).2), E'.evalEquiv_restrict,
    E.evalEquiv_restrict, evalEquiv_mapSections, twistMap_lTensor,
    E.transition_map E' φ hφ]

/-- **The morphism of descended presheaves of modules** induced by a map commuting with the
stratifications. -/
noncomputable def presheafMap (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) :
    E.presheaf ⟶ E'.presheaf where
  app X := ModuleCat.ofHom (E.mapSections E' φ hφ X.unop)
  naturality {X Y} f := by
    ext z
    exact (E.restrict_mapSections E' φ hφ f.unop z).symm

/-- The components of the induced morphism are `mapSections`. -/
@[simp] theorem presheafMap_app_apply (φ : M →ₗ[D] M')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m)) (X : 𝒜ᵒᵖ)
    (z : E.sections X.unop) :
    (E.presheafMap E' φ hφ).app X z = E.mapSections E' φ hφ X.unop z := rfl

/-- The morphism induced by the identity is the identity. -/
@[simp] theorem presheafMap_id
    (hφ : ∀ e m, E.str e (LinearMap.id m) = LinearMap.lTensor _ LinearMap.id (E.str e m)) :
    E.presheafMap E LinearMap.id hφ = 𝟙 _ := by
  ext X z
  exact Subtype.ext (funext fun p ↦ LinearMap.lTensor_id_apply _ _ _)

/-- The morphisms induced by maps compose. -/
theorem presheafMap_comp (φ : M →ₗ[D] M') (φ' : M' →ₗ[D] M'')
    (hφ : ∀ e m, E'.str e (φ m) = LinearMap.lTensor _ φ (E.str e m))
    (hφ' : ∀ e m, E''.str e (φ' m) = LinearMap.lTensor _ φ' (E'.str e m))
    (hφφ' : ∀ e m, E''.str e ((φ'.comp φ) m) = LinearMap.lTensor _ (φ'.comp φ) (E.str e m)) :
    E.presheafMap E'' (φ'.comp φ) hφφ' = E.presheafMap E' φ hφ ≫ E'.presheafMap E'' φ' hφ' := by
  ext X z
  exact Subtype.ext (funext fun p ↦ LinearMap.lTensor_comp_apply _ _ _ _)

end Stratification

end StratifiedDescent

end Crystalline
